(* ---------------------------------------------------------------------- *)
(* Existential Elimination Engine with backtracking                       *)
(* ---------------------------------------------------------------------- *)

open Constr
open Syntax
open IndexSyntax
open Ctx
open Support.Options
open Support.Error



let elim_debug   fi = message 4 General fi
let dp = Support.FileInfo.dummyinfo


let rec check_scope_ctx (in_ctx : 'a context ) (cs: constr) : bool =
  let fvars = constr_free_i_vars cs in
  let ctx = List.map fst (in_ctx.ivar_ctx @ in_ctx.evar_ctx) in
  List.fold_left (fun acc x ->  List.mem x ctx && acc) true fvars
             
          
let rec elim (in_ctx : 'a context) (c: constr) sc =
  match c with
  | CAnd(c1,c2) -> elim in_ctx c2 (fun x -> elim in_ctx c1 (fun y -> sc (CAnd(y,x))))
  | COr(c1,c2) ->  
    (* Order seems to matter here: "reverse" testcase finds the wrong
       substitution in cons boxed case when h is a boxed type *)
    elim in_ctx c1 (fun x -> elim in_ctx c2 (fun y -> sc (COr(y,x)) ))
    (* The following takes foreover to find the right side *)
    (* elim in_ctx c2 sc;  elim in_ctx c1 sc *)
  | CForall(bi_x, i, s, c') ->
    elim (extend_i_var bi_x.v_name  s in_ctx) c' (fun x -> sc (CForall(bi_x, i, s,x)) )
  | CExists(bi_x, i, s, c') ->
     let in_ctx' =  (extend_e_var bi_x.v_name s in_ctx) in
     elim in_ctx' c'
       (fun x ->
         elim_debug dp "Id:%a@ \n and x :%a@\n." Print.pp_vinfo bi_x Print.pp_cs x;
         if i = Support.FileInfo.NOCHANGE then sc (CExists(bi_x, i, s, x)) else
           (solve_sc x bi_x
              (fun witness () ->
                 match witness with
                 (* | IConst c when c < 0.0 -> () *)
                 | _ -> 
                   elim_debug dp "Witness %a, bi_x %a:@\n@ " Print.pp_iterm witness Print.pp_vinfo bi_x;
                   let c_subst = constr_simpl (constr_subst bi_x witness x) in                        
                   if (check_scope_ctx (in_ctx') c_subst) then
                     (elim_debug dp "Subst for %a :@\n@[%a@]@." 
                        Print.pp_vinfo bi_x Print.pp_cs c_subst;
                      sc c_subst) else ())
           );
         sc (CExists(bi_x, i, s, x)))
           
  | CImpl(c1,c2) -> elim in_ctx c2 (fun x -> sc (CImpl(c1,x)) )
  | _ -> sc c
and
  solve_sc (c: constr) (ex_var : var_info) ssc =
  let rec rec_match c ssc  =
    match c with
    | COr(c1,c2) 
    | CAnd(c1,c2) ->
      rec_match c2 ssc; rec_match c1 ssc
 
    | CImpl(c1,c2) -> rec_match c2 ssc
    | CLeq(IVar x1, IVar x2) 
    | CEq(IVar x1, IVar x2) ->
       (* Make sure that we don't substitute the same variable for itself *)
       if x1 = x2 then ()
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else ()


    (* | CLeq(IAdd(s1, IVar x), s2)  *)
    (* | CEq (IAdd(s1, IVar x), s2)  *)
    (* | CLeq(IAdd(IVar x, s1), s2)  *)
    (* | CEq (IAdd(IVar x, s1), s2)  ->  *)
    (*    if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2))  *)
    (*    then ssc (IMinus(s2, s1)) () else () *)
 
    | CBetaSub ( BVar x1, BVar x2)->elim_debug dp "Elim CBetaSub %a, %a :@\n@ " Print.pp_vinfo x1 Print.pp_vinfo x2;
      if x1 = x2 then ()
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else ()
    | CBetaEq ( BVar x1, BVar x2)->
      if x1 = x2 then ()
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else () 
    | CBetaSub ( BVar x, s)
    | CBetaSub (s, BVar x) -> elim_debug dp "Elim CBetaSub solo %a, :@\n@ " Print.pp_vinfo x ;
          if x = ex_var then ssc (IBeta s) () else ()
    | CEq(IVar x, s) 
    | CEq(s, IVar x) 
    | CLeq(IVar x, s) 
    | CLeq(s, IVar x) -> if x = ex_var then ssc s () else ()

    | CLeq(IMinus(IVar x, s1), s2) 
    | CEq (IMinus(IVar x, s1), s2) 
    | CEq (s1, IMinus(IVar x, s2))
    | CLeq(s1, IMinus(IVar x, s2)) -> 
       if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) 
       then ssc (IAdd(s1, s2)) () else ()

    | CEq(s, IMinus(IMinus(IVar x, s1), s2))
    | CLeq(s, IMinus(IMinus(IVar x, s1), s2)) when x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) -> ssc (IAdd(s, IAdd(s1, s2))) () 
 
   | CForall(x, i,s, c')   
   | CExists(x, i ,s, c') -> rec_match c' ssc

   | CEq(_,_) 
   | CLeq(_,_)
   | CTrue
   | CBetaSub (_,_)
   | CBetaEq (_, _)
   | CNot (_)
   | CBetaIn (_, _) 
   | CFalse 
   | _ -> ()
  
  in rec_match c ssc

  let rec elimt (in_ctx : 'a context) (c: constr) (sc: constr -> constr ) : constr =
  elim_debug dp "elimt : %a :@\n@ " Print.pp_cs c ;
  match c with
  | CAnd(c1,c2) -> elim_debug dp "CAnd1, c1: %a, c2: %a :@\n@ " Print.pp_cs c1 Print.pp_cs c2 ;
    let ret = elimt in_ctx c2 (fun x -> elimt in_ctx c1 (fun y -> elim_debug dp "CAnd2,x : %a, y: %a :@\n@ " Print.pp_cs x Print.pp_cs y  ;sc (CAnd(y,x))))  
        in  elim_debug dp "ret CAnd %a :@\n@ " Print.pp_cs ret; ret
  | COr(c1,c2) ->   
    (* Order seems to matter here: "reverse" testcase finds the wrong
       substitution in cons boxed case when h is a boxed type *)
    elimt in_ctx c1 (fun x -> elimt in_ctx c2 (fun y -> sc (COr(y,x)) ))
    (* The following takes foreover to find the right side *)
    (* elim in_ctx c2 sc;  elim in_ctx c1 sc *)
  | CForall(bi_x, i, s, c') ->
    elim_debug dp "Cforall 1, c': %a, bi_x':%a  :@\n@ " Print.pp_cs c' Print.pp_vinfo bi_x ;
    let ret = elimt (extend_i_var bi_x.v_name  s in_ctx) c' (fun x -> sc (CForall(bi_x, i, s,x)) )  
     in  elim_debug dp "ret CForall %a :@\n@ " Print.pp_cs ret; ret
  | CExists(bi_x, i, s, c') ->
  elim_debug dp "CEXIT 1, c': %a, bi_x':%a  :@\n@ " Print.pp_cs c' Print.pp_vinfo bi_x ;
     let in_ctx' =  (extend_e_var bi_x.v_name s in_ctx) in
      elimt in_ctx' c'
       (fun x ->
         elim_debug dp "Id:%a@ \n, and x :%a@\n." Print.pp_vinfo bi_x Print.pp_cs x;
         if i = Support.FileInfo.NOCHANGE || (not (solve_sc_b x bi_x)) then sc (CExists(bi_x, i, s, x)) else
            solve_sc2 x bi_x
              (fun witness () ->
                 match witness with
                 (* | IConst c when c < 0.0 -> () *)
                 | _ -> 
                  
                   let c_subst = constr_simpl (constr_subst bi_x witness x) in  
                    elim_debug dp "Witness %a, c_subst %a :@\n@ " Print.pp_iterm witness Print.pp_cs c_subst;                      
                   sc c_subst
                 )
          )
          
           
  | CImpl(c1,c2) ->
    elim_debug dp "CIMPL 1, c1: %a, c2:%a  :@\n@ " Print.pp_cs c1 Print.pp_cs c2 ;
   let ret = elimt in_ctx c2 (fun x -> sc (CImpl(c1,x)) ) in 
       elim_debug dp "ret cimpl %a :@\n@ " Print.pp_cs ret; ret
  | _ -> sc c
and
  solve_sc2 (c: constr) (ex_var : var_info) ssc : constr =
  let rec rec_match2 c ssc  =
    elim_debug dp "sc: %a :@\n@ " Print.pp_cs c;
    match c with
    | COr(c1,c2) 
    | CAnd(c1,c2) -> 
       let ret2 = 
     rec_match2 c2 ssc in 
     let ret1 =  rec_match2 c1 ssc in 
         elim_debug dp "sc2 cand ret1 %a, ret2: %a :@\n@, c1 :%a , c2 %a" Print.pp_cs ret1 Print.pp_cs ret2 Print.pp_cs c1 Print.pp_cs c2; 
         if (c1 != ret1) then ret1 else ret2
 
    | CImpl(c1,c2) -> let ret =  rec_match2 c2 ssc in 
          elim_debug dp "solve_sc2 c1: %a \n CIMPL %a :@\n@ " Print.pp_cs c1 Print.pp_cs ret; ret
    | CLeq(IVar x1, IVar x2) 
    | CEq(IVar x1, IVar x2) ->
       (* Make sure that we don't substitute the same variable for itself *)
       if x1 = x2 then c
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else c


    (* | CLeq(IAdd(s1, IVar x), s2)  *)
    (* | CEq (IAdd(s1, IVar x), s2)  *)
    (* | CLeq(IAdd(IVar x, s1), s2)  *)
    (* | CEq (IAdd(IVar x, s1), s2)  ->  *)
    (*    if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2))  *)
    (*    then ssc (IMinus(s2, s1)) () else () *)
 
    | CBetaSub ( BVar x1, BVar x2)->elim_debug dp "Elim CBetaSub %a, %a :@\n@ " Print.pp_vinfo x1 Print.pp_vinfo x2;
      if x1 = x2 then c
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else c
    | CBetaEq ( BVar x1, BVar x2)->
      if x1 = x2 then c
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else c 
    | CBetaSub ( BVar x, s)
    | CBetaSub (s, BVar x) -> elim_debug dp "Elim CBetaSub solo %a, :@\n@ " Print.pp_vinfo x ;
          if x = ex_var then ssc (IBeta s) () else c
    | CEq(IVar x, s) 
    | CEq(s, IVar x) 
    | CLeq(IVar x, s) 
    | CLeq(s, IVar x) -> if x = ex_var then ssc s () else c

    | CLeq(IMinus(IVar x, s1), s2) 
    | CEq (IMinus(IVar x, s1), s2) 
    | CEq (s1, IMinus(IVar x, s2))
    | CLeq(s1, IMinus(IVar x, s2)) -> 
       if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) 
       then ssc (IAdd(s1, s2)) () else c

    | CEq(s, IMinus(IMinus(IVar x, s1), s2))
    | CLeq(s, IMinus(IMinus(IVar x, s1), s2)) when x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) -> ssc (IAdd(s, IAdd(s1, s2))) () 
 
   | CForall(x, i,s, c')  -> let ret = rec_match2 c' ssc in  
   elim_debug dp "sc2 cexist %a :@\n@ " Print.pp_cs ret; ret
   | CExists(x, i ,s, c') -> let ret = rec_match2 c' ssc in  
   elim_debug dp "sc2 cforall%a :@\n@ " Print.pp_cs ret; ret

   | CEq(_,_) 
   | CLeq(_,_)
   | CTrue
   | CBetaSub (_,_)
   | CBetaEq (_, _)
   | CNot (_)
   | CBetaIn (_, _) 
   | CFalse 
   | _ -> c
  
  in rec_match2 c ssc

  and
  solve_sc_b (c: constr) (ex_var : var_info) : bool =
  let rec rec_match_b c  =
    elim_debug dp "sc_b: %a :@\n@ " Print.pp_cs c;
    match c with
    | COr(c1,c2) 
    | CAnd(c1,c2) -> 
       let ret2 = 
     rec_match_b c2  in 
     let ret1 =  rec_match_b c1 in 
      ret1 || ret2
 
    | CImpl(c1,c2) -> let ret2 = 
     rec_match_b c2  in 
     let ret1 =  rec_match_b c1 in 
      ret1 || ret2
    | CLeq(IVar x1, IVar x2) 
    | CEq(IVar x1, IVar x2) ->
       (* Make sure that we don't substitute the same variable for itself *)
       if x1 = x2 then false
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then true 
       else if x1 = ex_var then true else false


    (* | CLeq(IAdd(s1, IVar x), s2)  *)
    (* | CEq (IAdd(s1, IVar x), s2)  *)
    (* | CLeq(IAdd(IVar x, s1), s2)  *)
    (* | CEq (IAdd(IVar x, s1), s2)  ->  *)
    (*    if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2))  *)
    (*    then ssc (IMinus(s2, s1)) () else () *)
 
    | CBetaSub ( BVar x1, BVar x2)->elim_debug dp "Elim CBetaSub %a, %a :@\n@ " Print.pp_vinfo x1 Print.pp_vinfo x2;
      if x1 = x2 then false
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then  true  
       else if x1 = ex_var then  true else false
    | CBetaEq ( BVar x1, BVar x2)->
      if x1 = x2 then false
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then true  
       else if x1 = ex_var then true else false 
    | CBetaSub ( BVar x, s)
    | CBetaSub (s, BVar x) -> elim_debug dp "Elim CBetaSub 3 solo %a, :@\n@ " Print.pp_vinfo x ;
          if x = ex_var then true else false
    | CEq(IVar x, s) 
    | CEq(s, IVar x) 
    | CLeq(IVar x, s) 
    | CLeq(s, IVar x) -> if x = ex_var then true else false

    | CLeq(IMinus(IVar x, s1), s2) 
    | CEq (IMinus(IVar x, s1), s2) 
    | CEq (s1, IMinus(IVar x, s2))
    | CLeq(s1, IMinus(IVar x, s2)) -> 
       if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) 
       then true else false

    | CEq(s, IMinus(IMinus(IVar x, s1), s2))
    | CLeq(s, IMinus(IMinus(IVar x, s1), s2)) when x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) -> true 
 
   | CForall(x, i,s, c')  -> let ret = rec_match_b c'  in  
     ret
   | CExists(x, i ,s, c') -> let ret = rec_match_b c'  in  
     ret

   | CEq(_,_) 
   | CLeq(_,_)
   | CTrue
   | CBetaSub (_,_)
   | CBetaEq (_, _)
   | CNot (_)
   | CBetaIn (_, _) 
   | CFalse 
   | _ -> false
  
  in rec_match_b c 

