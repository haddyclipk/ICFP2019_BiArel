(* ---------------------------------------------------------------------- *)
(* Relational typechecking engine for BiArel                           *)
(* ---------------------------------------------------------------------- *)

open Tycheck

module BinaryTy =
struct
  type ty = Syntax.bi_ty
end
    

module AbstractBinary = TyCheck(BinaryTy)
     
open AbstractBinary
open Fresh_var
open Syntax
open IndexSyntax
open Constr
open Ctx
open Ty_error
open Support.FileInfo

module Opt = Support.Options
module Err = Support.Error


let dp = Support.FileInfo.dummyinfo
let b_debug   fi = Support.Error.message 4 General fi


let typing_error_pp = Err.error_msg_pp Opt.TypeChecker




 let  check_iarrays_sub (iarr_1: iterm) (iarr_2: iterm)  = 
   match iarr_1, iarr_2 with
      | IBeta b1, IBeta b2 ->  CBetaSub (b1 ,b2)

      |_ -> CTrue



 let ck_sub p1 p2 = 
     List.fold_left ( fun c (g, iarr) ->
             match List.assoc_opt g p2 with 
              | Some (iarr') -> CAnd (c, check_iarrays_sub iarr iarr') 
              | None -> CTrue
       ) CTrue  p1    

 let check_predicate_sub p1 p2 q1 q2 ctx : bool = 
   if (List.length p1) = (List.length p2) && (List.length q1) = (List.length q2) then 
      begin
        let c_1 = ck_sub p1 p2 in 
        let c_2 = ck_sub q1 q2 in
        let c= CImpl(c_1,c_2) in
       let c_3 =  CImpl (ctx.constr_env, c) in 
        let c_4 = quantify_all_exist ctx.evar_ctx c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
                            let w_c= WhyTrans.why3_translate_int c_5 in 
                           
                              WhySolver.post_st w_c 1      
      end
  else
     false   

     let get_fst c =
       match c with
       | CAnd(c1,c2) -> c1 
       | _ -> c

     let check_predicate_sub_cs p1 p2 q1 q2  = 
        let c_1 = ck_sub p1 p2 in 
        let c_2 = ck_sub q1 q2 in
        (* let c= CAnd( get_fst c_1, get_fst c_2) in *)
        let c= CAnd( c_1,  c_2) in
       c  

    let ck_submonad ia ia1 ia2 ia3 = 
      match ia ,ia1, ia2, ia3 with
      | IBeta b, IBeta b1 , IBeta b2, IBeta b3->  let unb = BUnion( b3, BUnion(b1,b2)) in  CBetaSub (unb, b) 

      |_ -> CTrue

   let sub_monad p1 p1' p q =
         List.fold_left ( fun c (g, iarr) ->
             match (List.assoc_opt g p1), (List.assoc_opt g p1') , (List.assoc_opt g p)  with 
              | Some (ia1),  Some (ia2), Some (ia3) -> CAnd (c, ck_submonad iarr ia1 ia2 ia3) 
              | _ -> CTrue
       ) CTrue  q  

    let rec expr_split (flg: bool) (e: expr)  : expr =
      let eps = expr_split flg in
      match e with
      | Var(_, v1) ->  e
      | Prim(_, p1)-> e
      | Fix(i,f1, x1, e1)-> Fix(i,f1, x1, eps e1)
      | FIXEXT (i,uty,f1, x1, e1)->  FIXEXT (i,uty,f1, x1, eps e1) 
      | Split (_, e1, c1) -> e 
      | Inl(i, e1) -> Inl(i, eps e1) 
      | Inr(i, e1) -> Inr(i, eps e1) 
      | Fst(i, e1) -> Fst(i, eps e1) 
      | Snd(i, e1) -> Snd(i, eps e1)
      | Pack(i, e1) -> Pack (i, eps e1) 
      | ILam(i, e1) -> ILam (i, eps e1) 
      | IApp(i, e1)-> IApp (i, eps e1) 
      | CExpr(i, e1) ->  CExpr(i, eps e1) 

      | App(i, e1, e2)-> App(i, eps e1, eps e2)  
      | Cons(i, e1, e2)-> Cons(i, eps e1, eps e2) 
      | Pair(i, e1, e2) -> Pair(i, eps e1, eps e2) 

      | Case(i, e, x, e1, y, e2)-> Case(i, eps e, x, eps e1, y, eps e2) 

      | CaseL(i, e, e1, h, tl, e2)-> CaseL(i,eps e, eps e1, h, tl, eps e2) 
      | Let (i, x, e1, e2) ->  Let (i, x, eps e1, eps e2)  
      | Unpack(i, e1, x, e2) -> Unpack(i, eps e1, x, eps e2)  
      | CLet (i, x, e1, e2) -> CLet (i, x, eps e1, eps e2) 
      | IfThen (i, e, e1, e2) -> IfThen (i, eps e, eps e1, eps e2) 
      | Nil i -> e
      | Contra i -> e 
      | UAnno(i, e1, uty, k) -> e
      | BAnno(i, e1, bty, k)-> e
      | BAnnoM(i, e1, bty1, bty2, k1,k2)-> if flg then BAnno (i, eps e1, bty1, k1) else BAnno (i, eps e1, bty2, k2)
   (*monadic expressions*)
      | Alloc(_,e1,e2) -> e
      | Update(_,e1,e2,e3) -> e 
      | Read(_,e1,e2)-> e
      | Return(_,e1)-> e
      | Letm (i, x, e1, e2) -> Letm (i, x, eps e1, eps e2) 
      | SWITCH (i, e1, bty, k, cs ) -> SWITCH (i, eps e1, bty, k, cs )
      | _ -> e

  let rec expr_switch (flg: bool) (e: expr)  : expr =
      let eps = expr_switch flg in
      match e with
      | Var(_, v1) ->  e
      | Prim(_, p1)-> e
      | Fix(i,f1, x1, e1)-> Fix(i,f1, x1, eps e1)
      | FIXEXT (i,uty,f1, x1, e1)->  FIXEXT (i,uty,f1, x1, eps e1) 
      | Split (_, e1, c1) -> e 
      | Inl(i, e1) -> Inl(i, eps e1) 
      | Inr(i, e1) -> Inr(i, eps e1) 
      | Fst(i, e1) -> Fst(i, eps e1) 
      | Snd(i, e1) -> Snd(i, eps e1)
      | Pack(i, e1) -> Pack (i, eps e1) 
      | ILam(i, e1) -> ILam (i, eps e1) 
      | IApp(i, e1)-> IApp (i, eps e1) 
      | CExpr(i, e1) ->  CExpr(i, eps e1) 

      | App(i, e1, e2)-> App(i, eps e1, eps e2)  
      | Cons(i, e1, e2)-> Cons(i, eps e1, eps e2) 
      | Pair(i, e1, e2) -> Pair(i, eps e1, eps e2) 

      | Case(i, e, x, e1, y, e2)-> Case(i, eps e, x, eps e1, y, eps e2) 

      | CaseL(i, e, e1, h, tl, e2)-> CaseL(i,eps e, eps e1, h, tl, eps e2) 
      | Let (i, x, e1, e2) ->  Let (i, x, eps e1, eps e2)  
      | Unpack(i, e1, x, e2) -> Unpack(i, eps e1, x, eps e2)  
      | CLet (i, x, e1, e2) -> CLet (i, x, eps e1, eps e2) 
      | IfThen (i, e, e1, e2) -> IfThen (i, eps e, eps e1, eps e2) 
      | Nil i -> e
      | Contra i -> e 
      | UAnno(i, e1, uty, k) -> e
      | BAnno(i, e1, bty, k)-> if flg then UAnno( i, eps e1, bi_ty_proj true bty,k ) else UAnno( i, eps e1, bi_ty_proj false bty,k )
      | BAnnoM(i, e1, bty1, bty2, k1,k2)-> e
   (*monadic expressions*)
      | Alloc(_,e1,e2) -> e
      | Update(_,e1,e2,e3) -> e 
      | Read(_,e1,e2)-> e
      | Return(_,e1)-> e
      | Letm (i, x, e1, e2) -> Letm (i, x, eps e1, eps e2) 
      | _ -> e


let rec lift2bi_ty (uty : un_ty) : bi_ty =
match uty with
| UTyPrim pty                 -> BTyPrim (lift_prim_bi_ty pty)
| UTyProd(uty1, uty2)         -> BTyProd (BTyBox(lift2bi_ty (uty1)), BTyBox(lift2bi_ty uty2))
| UTySum(uty1, uty2)          -> BTySum (BTyBox(lift2bi_ty uty1), BTyBox(lift2bi_ty uty2))
| UTyArr(uty1, _, _, uty2)    -> BTyArr (BTyBox (lift2bi_ty uty1), IZero, BTyBox (lift2bi_ty uty2))
| UTyForall(i, s, _, _, uty') -> BTyForall(i, s, IZero, BTyBox(lift2bi_ty uty'))
| UTyExists(i, s, uty')       -> BTyExists(i, s, BTyBox (lift2bi_ty uty'))
| UTyList(n, uty')            -> BTyList(n, IZero, BTyBox(lift2bi_ty uty'))
| UTyCs(c, uty')              -> BTyCs(c, BTyBox(lift2bi_ty uty'))
| UTyCsImp(c, uty')              -> BTyCsImp(c, BTyBox(lift2bi_ty uty'))



let push_box (bty: bi_ty) : bi_ty =
let aux bty =
  match bty with
  | BTyPrim pty -> bty
  | BTyProd(bty1, bty2)    -> BTyProd(BTyBox bty1, BTyBox bty2)
  | BTyArr(bty1, k, bty2)  -> BTyArr(BTyBox bty1, IZero, BTyBox bty2)
  | BTyForall(i, s, k, ty) -> BTyForall(i, s, IZero, BTyBox ty)
                                
  | BTyUnrel(UTyArr(uty1, _, _, uty2),
             UTyArr(uty1', _, _, uty2')) ->
    BTyArr(BTyBox(BTyUnrel(uty1, uty1')), IZero, BTyBox(BTyUnrel(uty2, uty2')))
  | BTyUnrel(UTyForall(i, s, _, _, ty),
             UTyForall(i', s', _, _, ty'))  ->
    BTyForall(i, s, IZero, BTyBox (BTyUnrel(ty,ty')))
  | BTyUnrel(UTyProd(uty1, uty2),
             UTyProd(uty1', uty2')) ->
    BTyProd(BTyBox(BTyUnrel(uty1,uty1')), BTyBox(BTyUnrel(uty2,uty2')))
  | BTyUnrel(UTyPrim pty1, UTyPrim pty2) when pty1 = pty2 -> BTyPrim (lift_prim_bi_ty pty1)
  | _ -> bty
in match bty with
  | BTyBox (BTyBox ty) -> aux ty
  | BTyBox ty -> aux ty
  | _ -> bty


(* Check whether bty1 is a subtype of bty2, generating the necessary constraints along the way. *)
let rec check_bsubtype (i: info) (bty1 : bi_ty) (bty2 : bi_ty) : constr checker =
  let fail = fail i @@ NotBSubtype (bty1, bty2) in
  b_debug dp " b ck subtupe :@\n@[bty1 is %a @]@\n,@[ bty2 is %a @]@." Print.pp_btype bty1 Print.pp_btype bty2 ;
   match bty1, bty2 with
  (* primitives *)
  | BTyPrim pty1, BTyPrim pty2 when pty1 = pty2 -> return_ch empty_constr
  | BTyPrim p, (BTyBox (BTyUnrel(UTyPrim p1, UTyPrim p2))) 
    when proj_prim_bi_ty p = p1 && p1 = p2-> return_ch empty_constr
  (* Lists *)
  | BTyList(n, alph, ty), BTyBox( BTyList(n', alph', ty')) ->
    check_size_eq n n' (check_size_eq alph (IZero) (check_bsubtype i (BTyBox ty) ty'))
  | BTyList (n, a,  ty1), BTyList (n', a', ty2) ->
    check_size_eq n n' (check_size_leq a a' (check_bsubtype i ty1 ty2))
  (* Sum and products *)
  | BTySum (ty1, ty2), BTySum (ty1',ty2')  -> check_bsubtype i ty1 ty1' >> check_bsubtype i ty2 ty2'
  | BTyProd (ty1, ty2), BTyProd (ty1',ty2') -> check_bsubtype i ty1 ty1' >> check_bsubtype i ty2 ty2'
  (* Fuction and forall types *)
  | BTyArr (ty1, k, ty2), BTyArr (ty1', k', ty2') ->
      check_size_leq k k' (check_bsubtype i ty1' ty1 >> check_bsubtype i ty2 ty2')
  | BTyForall (x,s, k, ty), BTyForall (x',s',  k', ty') ->
     if s = s' then
       let m = fresh_evar s in
       let x_m = IVar m in
       (m |::| s) i
          (check_size_leq (iterm_subst x x_m k) (iterm_subst x' x_m k')
              (check_bsubtype i (bi_ty_subst x x_m ty) (bi_ty_subst x' x_m ty')))
     else fail
 (* Existential types *)
  | BTyExists (x,s, ty), BTyExists (x',s', ty') ->
     if  x = x' && s = s' then
       (x |::| s) i (check_bsubtype i ty ty')
     else fail
 (* Constrained types *)
  | BTyCs(c1, ty1), BTyCs(c2, ty2) -> 
     check_bsubtype i ty1 ty2 >>=
       fun cs_b -> return_ch (CAnd(CImpl(c1, c2), cs_b))

  (* (\* Box Types *\) *)
 
  | BTyBox ty1, BTyBox (BTyBox ty2 as bty2') -> check_bsubtype i bty1  bty2'
   (* >||> check_bsubtype i ((\* push_box b *\)ty1) bty2 *)
  | BTyBox ty1, BTyBox ty2 -> check_bsubtype i (ty1) bty2 >||> check_bsubtype i ty1 ty2

  | BTyBox ty1, _ -> check_bsubtype i (push_box bty1) bty2 (* >||> check_bsubtype i ty1 bty2 *)

  (* Unrelated Types *)
  | BTyUnrel(uty1, uty2), BTyUnrel (uty1', uty2') -> check_unrel_subty i bty1 uty1 uty2
  | _, BTyUnrel (uty1, uty2) -> check_unrel_subty i bty1 uty1 uty2

   | BInt i_1, BInt i_2 -> check_size_leq i_1 i_2 (return_ch empty_constr)
   | BInt i, BTyPrim BPrimInt -> return_ch empty_constr
   | BArray (g,x,bty), BArray (g', x', bty') ->  
      if g = g' then 
        check_size_eq x x' (check_bsubtype i bty bty')
      else fail
  | BMonad(p_1, g_1,bty_1, k_1, q_1), BMonad(p_1', g_1', bty_1', k_1', q_1')->
   b_debug dp "BBMONAD SUBTYPE:@\n@[ bty1: %a, bty2: %a @]@." 
       Print.pp_btype bty1 Print.pp_btype bty2;
  fun (ctx, k) -> 
    if g_1 = g_1'  (* && (check_predicate_sub p_1' p_1 q_1 q_1' ctx) *)  then 
            match 
            ( check_size_leq k_1 k_1' (check_bsubtype i bty_1 bty_1') ) (ctx,k)
             with
            | Right c -> Right (merge_cs c (check_predicate_sub_cs p_1' p_1 q_1 q_1') )
            | Left err -> Left err
    else fail (ctx,k)
  | BTyUnrel (UMonad(p_1, g_1,uty_1, k_1, mu_1, q_1), UMonad(p_1', g_1', uty_1', k_1', mu_1', q_1')), BMonad(p, g,bty, k, q) ->
     b_debug dp "BMONAD SUBTYPE:@\n@[k is %a, k_1 is %a, k_1' is %a, bty is %a \n bty1: %a, bty2: %a @]@." 
       Print.pp_iterm k Print.pp_iterm k_1 Print.pp_iterm k_1' Print.pp_btype bty Print.pp_btype bty1 Print.pp_btype bty2;
       fun (ctx, k) ->
       if mu_1 = mu_1' then fail (ctx,k)
       else 
       begin
         match check_bsubtype i ( BTyUnrel (uty_1, uty_1')) bty (ctx, k) with
          | Right c -> let c1= sub_monad p p_1 p_1' q in
          b_debug dp "BMONAD SUBTYPE2:@\n@[c is %a,  c1 is %a @]@." Print.pp_cs c Print.pp_cs c1 ;

          Right (merge_cs c c1 )
          | Left err -> Left err
       end
          
  | BTyUnrel (UTyPrim UPrimUnit, UTyPrim UPrimUnit), BTyPrim BPrimUnit -> return_ch empty_constr
  | _, _ -> fail 


and check_unrel_subty  i bty uty1 uty2 = 
 fun(ctx, k) ->
       let ectx = Ctx.empty_context.var_ctx in
       let lctx = (set_ctx ectx ectx MaxEx ctx) in
       let rctx = (set_ctx ectx ectx MaxEx ctx) in
   match (Unary.check_usubtype i (bi_ty_proj true bty) uty1) (lctx, None) with
   | Right c1 ->
     begin
     match (Unary.check_usubtype i (bi_ty_proj false bty) uty2) (rctx, None) with
     | Right c2 -> Right (merge_cs c1 c2)
     | Left err' -> Left err'
     end
   | Left err -> Left err
                 
(** [inferType e] infers that expression [e] has type [bi_ty] along with
    cost [k] in context [ctx]. If it does,
    it returns [bi_ty inferer: (bi_ty, k, psi)] where all the free
    existential variables occuring in bi_ty and k are declared in
    psi, otherwise it raises an exception. *)
let rec inferBType (ePair: expr * expr) : ty inferer  =
  b_debug dp "infB:@\n@[e is %a @]@." Print.pp_expr (fst ePair);
  match ePair with
  | Var (i1, vi1), Var(i2, vi2) -> 
  b_debug dp "var:@\n@[v1 is %a @]@." Print.pp_expr (fst ePair);
    if vi1 = vi2
    then 
    (get_var_ty i1 vi1 <<= fun y ->  (return_inf y)) 
    else infer_unrel (fst ePair) (snd ePair)
  | Prim (i1, ep1), Prim (i2, ep2) -> 
    if ep1 = ep2 then return_inf(BTyBox (bi_type_of_prim ep1))
    else infer_unrel (fst ePair) (snd ePair)
  | Fst(i1, e1), Fst(i2, e2) -> infer_handle_unrel ePair (inferBType (e1,e2) <<= infer_proj i1 fst)
  | Snd(i1, e1), Snd(i2, e2) -> infer_handle_unrel ePair (inferBType (e1,e2) <<= infer_proj i2 snd)
  | App (i, e1, e2), App (i', e1', e2') -> infer_app (inferBType (e1, e1')) i (e2, e2') ePair
  | IApp (i1, e1), IApp(i2, e2) -> infer_iapp (inferBType (e1,e2)) i1 ePair
  | BAnno (i1, e1, bty1, k1), BAnno (i2, e2, bty2, k2) ->
    if bty1 = bty2 && k1 = k2 then infer_check_anno i1 e1 e2 bty1 k1
    else fail (expInfo e1) (Internal ("Types and costs should match in annotated expressions!"))

 | BAnnoM (i1, e1, bty1, bty1',k1, k1'), BAnnoM (i2, e2, bty2,  bty2',k2, k2') ->
    if bty1 = bty2 && k1 = k2 && k1'=k2' && bty1' = bty2' then infer_check_annoM i1 e1 e2 bty1 k1 bty1' k1'
    else fail (expInfo e1) (Internal ("Types and costs should match in annotated monad expressions!"))

  | CExpr (i1, e1), CExpr(i2, e2) ->  b_debug dp "inf_celim :@\n@[e is %a @]@."  Print.pp_expr e1; infer_celim (inferBType (e1,e2) ) i1 
  |  _ -> infer_unrel (fst ePair) (snd ePair)

and infer_check_annoM i e1 e2 bty1 k1 bty1' k1' =
  fun ctx ->
    (*TODO: only if nocost is disabled*)
    b_debug dp "annoM1:@\n@[k1 is %a, e1 is %a,  bty1 is %a , bty1' is %a @]@." 
  Print.pp_iterm k1 Print.pp_expr e1 Print.pp_btype bty1  Print.pp_btype bty1';
    match checkBType (e1 , e2) bty1 ( ctx, Some k1 ) with
    | Right c -> Right (bty1, c, [], Some k1)
    | Left err -> 
      begin
  b_debug dp "annoM2:@\n@[k1 is %a, k1' is %a,  bty1 is %a , bty1' is %a @]@." 
  Print.pp_iterm k1 Print.pp_iterm k1' Print.pp_btype bty1  Print.pp_btype bty1;
        match checkBType (e1,e2) bty1' (ctx, Some k1') with
        | Right c' -> Right (bty1', c', [], Some k1')
        | Left err' -> Left err'
      end

and infer_celim m i = 
   fun ctx -> 
      match m ctx with
    | Right (bty, c, psi, k) ->
      begin
        match bty with
        | BTyCsImp(c_1,bty_1) ->
            b_debug dp "binary celim : psi is @[ %a @] @." Print.pp_ivar_ctx psi;
            Right ( bty_1 , (CImpl(c_1, c) ) ,  psi, k)
        | _ -> fail i (WrongBShape (bty, "binary celim fails ")) ctx
      end
    | Left err -> Left err

and infer_unrel e1 e2 = 
  fun ctx -> 
    let u1ctx = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.var_ctx in
    let u2ctx = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.var_ctx in
    let u1ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.uvar_ctx in
    let u2ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.uvar_ctx in
     let u1 = union_ctx u1ctx u1ctx' in 
    let u2 = union_ctx u2ctx u2ctx' in 
    let lctx = (set_ctx u1 u1ctx' MaxEx ctx) in
    let rctx = (set_ctx u2 u2ctx' MinEx ctx) in
    let r = Unary.inferUType e1 (lctx) in
    match r with
    | Right (uty1, c1, ex_ctx1, k1) ->
      begin
        match Unary.inferUType e2 (rctx) with
        | Right (uty2, c2, ex_ctx2, k2) -> 
          Right (BTyUnrel(uty1, uty2), merge_cs c1 c2, ex_ctx1 @ ex_ctx2, option_combine k1 k2 (fun (x,y) -> IMinus(x,y)))
        | Left err -> Left err
      end
    | Left err -> Left err

and infer_check_anno i e1 e2 bty k =
  fun ctx ->
    (*TODO: only if nocost is disabled*)
    match checkBType (e1, e2) bty (ctx, Some k) with
    | Right c -> Right (bty, c, [], Some k)
    | Left err -> Left err


and infer_iapp m i eP =
  fun ctx ->
    match m ctx with
    | Right (bty, c, psi, k) ->
      begin
        match push_box bty, k with
        | BTyForall(x, s, k_e, ty), k->
          let v = fresh_evar s in
          let witn = IVar v in
           b_debug dp "iapp, witn is %a" Print.pp_iterm witn;
          Right (bi_ty_subst x witn ty, c, (v,s):: psi, 
		 Core.Option.map ~f:( fun k -> add_costs(k, iterm_subst x witn k_e)) k)
        | BTyUnrel(uty1, uty2) , _-> infer_unrel (fst eP) (snd eP) ctx
        | _ -> fail i (WrongBShape (bty, "index quantified (forall) ")) ctx
      end
    | Left err -> Left err


and infer_handle_unrel eP  (m: ty inferer) : ty inferer =
  fun ctx ->
    let mc = m ctx in 
    match mc with
    | Left err' when err'.v = Ty_error.SwitchPMatch -> infer_unrel (fst eP) (snd eP) ctx
    | _ ->  mc

and infer_app m i eP2 eP =
  infer_handle_unrel eP (m =<-> (fun inf_bty heur ->
      let pbty = push_box inf_bty in
       b_debug dp "inf_app:@\n@[pbty is %a, inf_bty: %a @]@." Print.pp_btype pbty Print.pp_btype inf_bty;
      match inf_bty, heur with
      | BTyBox (BTyArr(ty1, k'', ty2) ), NoChange
      | BTyArr(ty1, k'', ty2), _ -> [(checkBType eP2 ty1, ty2, k'')]
      | BTyBox(BTyUnrel(_,_)), NoChange
      | BTyUnrel(_,_), _ -> [(fail i SwitchPMatch, BTyPrim (BPrimInt), IZero)]
      | _ -> 
      begin
        match pbty, inf_bty with
        | BTyArr(pty1, pk'', pty2), BTyBox(BTyUnrel(_)) -> 
          [(checkBType eP2 pty1, pty2, pk''); (fail i SwitchPMatch, BTyPrim (BPrimInt), IZero)]
        | BTyArr(pty1, pk'', pty2), BTyBox(BTyArr(ty1, k'',ty2)) -> 
         b_debug dp " if_app box function :@\n@[pk'' is %a, pty1: %a, k'' is %a, ty1: %a @]@." Print.pp_iterm pk'' Print.pp_btype pty1 Print.pp_iterm k''  Print.pp_btype ty1 ;
        [(checkBType eP2 pty1, pty2, pk''); (checkBType eP2 ty1, ty2, k'')]
        | _ -> [(fail i (WrongBShape (inf_bty, "function app")), BTyPrim (BPrimInt), IZero)]
      end
    ))

and infer_proj i f =
  fun bty ->
    match push_box bty with
    | BTyProd (ty1, ty2) ->  return_inf(f (ty1, ty2))
    | BTyUnrel(_) -> fail i Ty_error.SwitchPMatch
    | _ -> fail i (WrongBShape (bty, "product"))

(** [checkBType e] verifies that expression [e] has unary type [bty]
    in the context [ctx] with the cost [k]. If
    it does, it returns unit, otherwise it raises an exception. *)
and checkBType (ePair : expr * expr) (bty : ty) : constr checker =
   b_debug dp " checkBType :@\n@[e is %a, ty: %a @]@." Print.pp_expr (fst ePair) Print.pp_btype bty;
  match ePair, bty with
  (* Switch to unary mode for constructors typed with U(A1,A2) *)
  | (Fix(_, _, _, _), Fix(_, _, _, _)), BTyUnrel(uty1,uty2)
  | (Nil _, Nil _),  BTyUnrel(uty1,uty2) 
  | (Pair(_,_,_), Pair(_,_,_)), BTyUnrel(uty1,uty2)
  | (Cons(_,_,_), Cons(_,_,_)), BTyUnrel(uty1,uty2)
  | (Inl(_,_), Inl(_,_)), BTyUnrel(uty1,uty2)
  | (Inr(_,_), Inr(_,_)), BTyUnrel(uty1,uty2)
  | (ILam(_,_), ILam(_,_)), BTyUnrel(uty1,uty2)
  | (Pack(_,_), Pack(_,_)), BTyUnrel(uty1,uty2) -> check_unrel (fst ePair) (snd ePair) uty1 uty2

  (* Constrained type intro *)
  | _, BTyCs(c, ty) -> checkBType ePair ty >>=
			 fun cs_b -> return_ch (CAnd(c, CImpl(c, cs_b)))

  | _, BTyCsImp (c, ty) ->  (with_new_ctx (fun ctx -> {ctx with constr_env = CAnd (c, ctx.constr_env )} ) (checkBType ePair ty) )
                            >>= fun cs_b -> return_ch (CImpl(c, cs_b))

  (* Primitive expressions *)
  | (Prim (i, ep1), Prim (i', ep2)), tp when tp = bi_type_of_prim ep1 && ep1 = ep2 -> 
    return_leaf_ch 
  |  (Fix(i1, vi_f1, vi_x1, e1), Fix(i2, vi_f2, vi_x2, e2)), _
    when vi_f1 = vi_f2 && vi_x1 = vi_x2 -> check_fix i1 vi_f1 vi_x1 (e1, e2) bty
  (* List type expressions *)
  | (Nil i1, Nil i2),  _ -> check_nil i1 bty
  | (Cons(i, e1, e2), Cons(i', e1', e2')), _ -> check_cons (e1, e1') (e2, e2') i bty
  | (CaseL(i,e, e_n, x_h, x_tl, e_c), CaseL(i',e', e_n', x_h', x_tl', e_c')), _
    when x_h = x_h' && x_tl = x_tl' ->
    check_case_list(* _heuristic *) i (e,e') (e_n,e_n') x_h x_tl (e_c, e_c') bty
  (* Sum type expressions *)
  | (Inl(i1, e1), Inl(i2, e2)), BTySum (ty1,_) -> checkBType (e1, e2) ty1
  | (Inr(i1, e1), Inr(i2, e2)), BTySum (_,ty2) -> checkBType (e1, e2) ty2
  | (Case(i,e, x_l, e_l, x_r, e_r), Case(i',e', x_l', e_l', x_r', e_r')), _
    when x_l = x_l' && x_r = x_r' -> check_case_sum i (e, e') x_l (e_l, e_l') x_r (e_r, e_r') bty
  (* If statement *)
  | (IfThen(i, e, el, er), IfThen(i', e', el', er')), _ -> check_if i (e, e') (el, el') (er, er') bty ePair
  (* Pairs *)
  | (Pair(i, e1, e2), Pair(i', e1', e2')), _ ->
    let pbty = push_box bty in
    begin match pbty with
      | BTyProd (ty1,ty2) -> (checkBType (e1, e1') ty1) >> (checkBType (e2, e2') ty2)
      | _ -> fail i (WrongBShape (bty, "product"))
    end
  (* Index abstraction *)
  | (ILam (i, e),  ILam (i', e')), BTyForall(x, s, k, ty) ->
    check_body ((x |::| s) i (checkBType (e, e') ty)) k
  (* Existential introduction and elimination *)
  | (Pack (i, e), Pack (i', e')), _ -> check_pack i (e, e') bty
  | (Unpack (i, e1, vi_x, e2), Unpack (i', e1', vi_x', e2')), _ 
    when vi_x = vi_x' -> check_unpack i (e1, e1') vi_x (e2, e2') bty
  (* Let bound *)
  | (Let (i, vi_x, e1, e2), Let (i', vi_x', e1', e2')), _ 
    when vi_x = vi_x' ->
    inferBType (e1, e1') <->=
    (fun bty_x -> (vi_x |:| bty_x) (checkBType (e2, e2') bty))
  (* Constrained type elim *)
  | (CLet (i, vi_x, e1, e2), CLet (i', vi_x', e1', e2')), _ 
    when vi_x = vi_x' -> check_clet i vi_x (e1, e1') (e2, e2') bty
  (* Contra returns immediately *)
  | (Contra i, Contra i'),  _ -> return_ch empty_constr
					   
 (*  | Let(i, vi_x, e1, e2), e, _ -> check_let_asynch i vi_x e1 e2 e *)

  | (Alloc (i, e1, e2), Alloc (i', e1', e2') ) , BMonad(p,g, bty, k, q) ->  
      check_alloc (e1,e1') (e2,e2') p g q bty i k

  | (Read (i, e1, e2)  , Read (i', e1', e2') ) ,  BMonad(p,g, bty, k, q) ->
       check_read (e1,e1') (e2,e2') p g q bty i k

  | (Return (i, e1) ,Return (i', e1') ) ,  BMonad(p,g, bty, k, q) ->
       check_return (e1,e1')  p g q bty i k

  |  ( Update(i, e1, e2, e3),  Update(i', e1', e2', e3') ),  BMonad(p,g, bty, k, q) ->
      begin
      match bty with
      | BTyPrim (BPrimUnit) ->  
          check_update (e1,e1') (e2,e2') (e3,e3') p g q bty i k
      | BTyUnrel (UTyPrim UPrimUnit, UTyPrim UPrimUnit ) ->  
         check_update (e1,e1') (e2,e2') (e3,e3') p g q bty i k
      | _ -> fail i (WrongBShape (bty, "b update type not unit"))
      end

  | (Letm(i, x, e1, e2), Letm(i', x', e1', e2') ),    BMonad(p,g, bty, k, q) ->
      (inferBType (e1, e1') ) <->=
       ( fun bty_inf ->
         match bty_inf with
         |  BMonad (p_1, g_1, bty_1, k_1, q_1) ->
             begin
            
       b_debug dp "B let second premise :@\n@[k_1 is %a, k is %a,  next bty is %a  @]@." Print.pp_iterm k_1 Print.pp_iterm k Print.pp_btype bty;
             (x |:| bty_1 ) ( checkBType (e2,e2') (BMonad( q_1 , g, bty, (minus_cost k k_1),  q  ) ) )
             end
         | _ -> fail i (WrongBShape (bty, "Let monadic"))    
       )

   | ( Split (i, e1, c1), Split (i', e1', c1') ), _ 
      when (c1 = c1') ->  
      b_debug dp "B split:@\n@[bty: %a, e1: %a  @]@." Print.pp_btype bty Print.pp_expr e1;
      check_split e1  e1' c1 bty i 

  |  (FIXEXT(i1, uty1, vi_f1, vi_x1, e1), FIXEXT(i2, uty2, vi_f2, vi_x2, e2)), _  
     when vi_f1 = vi_f2 && vi_x1 = vi_x2 -> 

      (vi_f1 |:-| BTyUnrel(uty1,uty2)) (check_fix i1 vi_f1 vi_x1 (e1, e2) bty)

  | (SWITCH (i1, e1, bty1,k1,c1), SWITCH (i2,e2, bty2,k2,c2) ), _  
      when (bty1 = bty2) && (c1 =  c2 ) ->  
  b_debug dp "SWITCH :@\n@[e1:%a + bty1:%a + c1 : %a, e2: %a + bty2:%a+ c2: %a @]@." 
  Print.pp_expr e1 Print.pp_btype bty1 Print.pp_cs c1 Print.pp_expr e2 Print.pp_btype bty2 Print.pp_cs c2;

  (
    check_switch e1 e2 bty1 k1 k2 c1 bty)
   >&&> (check_bsubtype i1 bty1 bty )
 
  (* Switch to inference *)
  |  _, _ -> infer_and_check (expInfo (fst ePair)) ePair bty


(* and check_let_asynch i vi_x e1 e2 e = 
    inferBType (e1, e1') <->=
    (fun bty_x -> (vi_x |:| bty_x) (checkBType (e2, e2') bty))
 *)

 and sat c ctx =
                      let c_3 =  CImpl (ctx.constr_env, c) in 
                        let c_4 = quantify_all_exist ctx.evar_ctx c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
                            let w_c= WhyTrans.why3_translate_int c_5 in 
                            b_debug dp "b sat  : @[  w_c: %a @]"  Why3.Pretty.print_term w_c;
                              WhySolver.post_st w_c 1




 and  check_switch e1 e2 bty1 k1' k2' cs bty = 
    fun(ctx, k) ->
    b_debug dp "@\n@[SWITCH another branch: e:%a , constr_env : %a @]@." Print.pp_expr e1 Print.pp_cs ctx.constr_env ;
    if (sat cs ctx) then 
  begin
      
    b_debug dp "SWITCH ck:@\n@[bctx:%a, buctx : %a  @]@." Print.pp_var_bctx ctx.var_ctx Print.pp_var_bctx ctx.uvar_ctx;
    let uty1 = bi_ty_proj true bty1 in 
    let uty2 = bi_ty_proj false bty1 in 
    let u1ctx = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.var_ctx in
    let u2ctx = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.var_ctx in
     let u1ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.uvar_ctx in
    let u2ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.uvar_ctx in
    let u1 = union_ctx u1ctx u1ctx' in 
    let u2 = union_ctx u2ctx u2ctx' in 
    let lctx = (set_ctx u1 u1ctx' MaxEx ctx) in
    let rctx = (set_ctx u2 u2ctx' MinEx ctx) in
    let ep1 = expr_switch true e1 in 
    let ep2 = expr_switch false e2 in
    (* let v' = fresh_evar Cost in
    let k' = IVar v' in
    let kl_ctx = Core.Std.Option.value_map ~default:lctx ~f:(fun _ -> extend_e_var v'.v_name Cost lctx) k in
    let kr_ctx = Core.Std.Option.value_map ~default:rctx ~f:(fun _ -> extend_e_var v'.v_name Cost rctx) k in *)
    let k1 = Core.Option.map ~f:(fun _ -> k1') k in
    let k2 = Core.Option.map ~f:(fun _ -> k2') k in
    b_debug dp "SWITCH check unrel :@\n@[UTY1: %a e1:%a, ep1 :%a @]@." Print.pp_utype uty1 Print.pp_expr e1 Print.pp_expr ep1 ;
     b_debug dp "@\n@[SWITCH3 : utc:%a @]@." Print.pp_var_uctx u1 ;
    begin
      match Unary.checkUType ep1 uty1 (lctx, k1) with
      | Right c1 -> b_debug dp "SWITCH check unrel2 :@\n@[c1:%a  @]@." Print.pp_cs c1  ;
        let ret1 = Exist_elim.elimt lctx c1 (fun x -> x) in 
          let w_c= WhyTrans.why3_translate ret1 in 
                            b_debug dp "b switch  : @[ ret1:%a, w_c: %a @]" Print.pp_cs ret1 Why3.Pretty.print_term w_c;
                          let ret2 =   WhySolver.post_st w_c 1 in
         begin
           match Unary.checkUType ep2 uty2 (rctx, k2) with
           | Right c2 -> 
                       let ret3 = Exist_elim.elimt rctx c2 (fun x -> x) in 
          let w_c2= WhyTrans.why3_translate ret3 in 
                            b_debug dp "b switch2  : @[  w_c: %a @]"  Why3.Pretty.print_term w_c2;
                          let ret4 =   WhySolver.post_st w_c2 1 in
                         if(ret2 && ret4) then Right(merge_cs CTrue c1(*c1*) ) else Right (merge_cs c1 c2)
           | Left err -> Left err
         end
      | Left err -> Left err
    end
  end
else   
      (checkBType (e1,e2) bty) (ctx, k)

and check_split e1 e2 (c: constr) bty i = 
    ( with_new_ctx (fun ctx -> {ctx with constr_env = CAnd (c, ctx.constr_env )} )  (checkBType ((expr_split true e1), (expr_split true e2)) bty)   
     >>= fun cs_b -> return_ch (CImpl(c, cs_b)) )
    >&&>
    ( with_new_ctx (fun ctx -> {ctx with constr_env = CAnd (CNot c , ctx.constr_env )} )  (checkBType ((expr_split false e1), (expr_split false e2)) bty) 
     >>= fun cs_b -> return_ch (CImpl( CNot c, cs_b))
    )


and check_update (eP1: expr * expr) (eP2: expr * expr) (eP3: expr * expr) (p:predicate) g (q:predicate) bty i (k_m:iterm) =
     fun (ctx,k) -> match (inferBType eP1  ctx) with
                    | Right (bty_1, c_1, psi_1, k_1) ->

                        begin
                          b_debug dp "b update first premise :@\n@[type is %a, predicate is %a, eP3: %a @]@."
                            Print.pp_btype bty_1  Print.pp_predicates p Print.pp_expr (fst eP3);
                         match bty_1 with
                         | BArray (g, l, bty') ->
                            if (List.mem_assoc g p) then
                               begin
                              match (inferBType eP2 ctx) with
                              | Right (bty_2, c_2, psi_2, k_2) ->
                                 begin
                                 match bty_2 with
                                  | BInt (l') -> 
                                        let k_sum = option_combine k_1 k_2 (fun (ik,k') -> add_costs(ik, k') ) in
                                        let k_3 = option_combine (Some k_m) k_sum (fun(ik, k') -> IMinus(ik, k')  ) in
                                        b_debug dp "b update :@\n@[k is %a, k_sum is %a, k_3 is %a @]@." 
                                        Print.pp_cost k Print.pp_cost k_sum Print.pp_cost k_3 ;

                                        if  (predicate_updateB p g q l' l ctx i psi_2 c_2)
                                        then
                                      
                                          begin
                                        match (checkBType eP3 (BTyBox bty')  (ctx, k_3)) with
                                        | Right (c_3) -> 
                              b_debug dp "updtB pass, check :@\n@[eP3 :%a, box bty': %a, @]@."
                            Print.pp_expr (fst eP3) Print.pp_btype bty';
                                        Right (      quantify_all_exist (psi_1@psi_2) (merge_cs c_1 (merge_cs c_2 c_3) ) )
                                        | Left err'' -> Left err''
                                          end
                                        else
                                           begin
                                             if (predicate_update p g q l' l ctx i psi_2 c_2)
                                             then
                                             
                                            match (checkBType eP3 ( bty')  (ctx, k_3)) with
                                            | Right (c_3) -> 
                                             b_debug dp "updtB fails, check :@\n@[eP3 :%a, box bty': %a, @]@."
                            Print.pp_expr (fst eP3) Print.pp_btype bty';
                                            Right (      quantify_all_exist (psi_1@psi_2) (merge_cs c_1 (merge_cs c_2 c_3) ) )
                                            | Left err'' -> Left err''

                                            else fail i (WrongBShape (bty_2, " both predicate update fails")) ctx
                                           end
                                              
                                    
                                    
                                      | _ -> fail i (WrongBShape (bty_2, "b update second premise not BINT")) ctx
                                     end 
                                 | Left err' -> Left err'      
                                  end
                            
                            else fail i (WrongBShape (bty_1, "gamma not in predicate p")) ctx
                        
                         | _ -> fail i (WrongBShape (bty, "b updt first premise fails")) ctx
                        end
                   | Left err -> Left err

and predicate_update p g q l' l ctx i psi_2 c2 =
  let ibeta =  (List.assoc_opt g p) in
  let ibeta'  = (List.assoc_opt g q) in
  b_debug dp "predicate update";
  match ibeta, ibeta' with
  | Some (IBeta beta), Some (IBeta beta') ->
     let c_1 = (* CBetaEq *) CBetaSub ( BUnion(beta, BPos l' ), beta' ) in
        let c_2 =   merge_cs c2 (merge_cs  (CLeq (l', l)) c_1 )in 
                      let c_3 =  CImpl (ctx.constr_env, c_2) in 
                        let c_4 = quantify_all_exist (ctx.evar_ctx@ psi_2) c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx  c_4 in
                          let elim_c5 =  Exist_elim.elimt ctx c_5  
                            (fun cs' ->
                               cs'
                              ) in 
                            b_debug dp "updtB3 : @[ elim_c_5: %a @]"   Print.pp_cs elim_c5;
                            let w_c= WhyTrans.why3_translate(* _int *) elim_c5 in 
                            b_debug dp "b predicate_updt  : @[  w_c: %a @]"  Why3.Pretty.print_term w_c;
                              WhySolver.post_st w_c 1
  | _, _ -> false   
  
                                                               
and predicate_updateB p g q l' l ctx i psi_2 c2=
  let ibeta =  (List.assoc_opt g p) in
  let ibeta'  = (List.assoc_opt g q) in
  b_debug dp "predicate updateB" ;
  match ibeta, ibeta' with
  | Some (IBeta beta), Some (IBeta beta') ->
     let c_1 = CBetaEq (beta', BSetDiff(beta, BPos l' ) ) in
        let c_2 = merge_cs c2 (merge_cs  (CLeq (l', l)) c_1 )in 
                      let c_3 =  CImpl (ctx.constr_env, c_2) in 
                        let c_4 = quantify_all_exist (ctx.evar_ctx@ psi_2) c_3 in 
                          let c_5 = quantify_all_universal (ctx.ivar_ctx ) c_4 in
                          b_debug dp "updtBb : @[ c_5: %a @]"   Print.pp_cs c_5;
                            let elim_c5 =  Exist_elim.elimt ctx c_5  
                            (fun cs' ->
                               cs'
                              ) in 
                            b_debug dp "updtB3 : @[ elim_c_5: %a @]"   Print.pp_cs elim_c5;
                            let w_c= WhyTrans.why3_translate_int elim_c5 in 
                            b_debug dp "handler_u_updte3 : @[  w_c: %a, c_5: %a @]"  
                            Why3.Pretty.print_term w_c Print.pp_cs c_5;
                              WhySolver.post_st w_c 1
  | _, _ -> false   
                                                              
                                                        
           
and check_return  (eP1: expr * expr)  (p:predicate) g (q:predicate) bty i (k:iterm) =
  fun (ctx, k')->
  b_debug dp "ck return, @[ p is %a, q is %a, eP1 is %a @]@." Print.pp_predicates p Print.pp_predicates q Print.pp_expr (fst eP1);
   if (predicate_return p  q ctx) || (predicate_return q  p ctx) then
                   ( check_body (checkBType eP1 bty ) k ) (ctx,k')
                  else
                    fail i (WrongBShape (bty, "b ck return fails")) (ctx,k')
  
and predicate_return p  q ctx =
  if (List.length p) = (List.length q) then 
         List.for_all (fun (g, iarr) ->
             match List.assoc_opt g q with 
              | Some (iarr') ->  Unary.check_iarrays_sub iarr iarr' ctx 
              | None -> false
          ) p
      else false 
(* and  check_iarrays_eq (iarr_1: iterm) (iarr_2: iterm) : bool = 
     match iarr_1, iarr_2 with
      | IBeta b1, IBeta b2 ->  check_beta_eq b1 b2
      |_ -> false

and  check_beta_eq (b1:beta) (b2:beta) : bool =
    match b1, b2 with
     | BIO, BIO ->  true
     | BVar v1, BVar v2 -> v1 = v2
     | BRange (i1, i2), BRange(i1',i2') -> ( (iterm_simpl i1) = (iterm_simpl i1')  ) && (  (iterm_simpl i2) = (iterm_simpl i2') )
     | BPos i1, BPos i2 -> (iterm_simpl i1) = (iterm_simpl i2)
     | BUnion (b1,b2), BUnion (b1',b2') -> (check_beta_eq b1 b2) && (check_beta_eq b1' b2')
     | BIntersect (b1,b2), BIntersect (b1',b2') -> (check_beta_eq b1 b2) && (check_beta_eq b1' b2')
     | BSetDiff (b1,b2), BSetDiff (b1',b2') -> (check_beta_eq b1 b2) && (check_beta_eq b1' b2')
     | _ -> false *)

(* and beta_simpl (b:beta) : beta =
 *   match beta with
 *   | BUnion (BRange(i1,i2), BIO ) *)
           
and check_read (eP1: expr * expr) (eP2: expr * expr) (p:predicate) g' (q:predicate) bty i' (k:iterm) =
   fun (ctx,k) -> match (inferBType eP1  ctx) with
                 | Right (bty_1, c_1, psi_1, k_1) ->
                    begin
                      b_debug dp "b read first premise :@\n@[type is %a, eP2 is %a @]@."
                        Print.pp_btype bty  Print.pp_expr (fst eP2);
                         match bty_1 with
                         | BArray (g, l, bty') ->
                          
                          if (List.mem_assoc g p) then
                            begin
                              match (inferBType eP2 ctx) with
                              | Right (bty_2, c_2, psi_2, k_2) ->
                                                 begin
                                                   let k_sum =  option_combine k_1 k_2 (fun (ik,k') -> add_costs(ik, k')) in
                                                   let k_leq =  option_combine k_sum k (fun (ik,k') -> cost_cs ctx(ik, k')) in
                                                   let k_cs = Core.Option.value_map ~default:CTrue
      				                                ~f:(fun k -> k) k_leq in
                                                 
                                                   match bty_2 with
                                                   | BInt (l') ->
                                                    b_debug dp "b read second premise :@\n@[l' is %a, psi is %a, bty :%a @]@."
                                                    Print.pp_iterm l' Print.pp_ivar_ctx (psi_1@psi_2) Print.pp_btype bty;
                                                      if bty = (BTyBox bty') && (predicate_readB p g q  l' l ctx (psi_1@psi_2) i') then 
                                                    
                                                    Right (  quantify_all_exist (psi_1@psi_2) ( merge_cs k_cs (  merge_cs c_1 c_2  ) )    )
                                                      else  
                                                         begin
                                                             if (bty = bty') && (predicate_read p g q  l' l ctx (psi_1@psi_2) i' c_2) then          
                                                       Right (  quantify_all_exist (psi_1@psi_2) ( merge_cs k_cs  (merge_cs c_1 c_2) )     )
                                                             else  let err'' = {i =i'; v =  (WrongBShape (bty, "read predicate box premise fails")) } 
                                                           in Left err''
                                                         end
                                                       
                                                    | _ -> fail i' (WrongBShape (bty, " can not find read rules")) ctx
                                                   end     
                                                  
                                                
                            | Left err' -> Left err'
                           end
                          else fail i' (WrongBShape (bty_1, "gamma not in predicate read")) ctx
                        
                         | _ -> fail i' (WrongBShape (bty, "read first premise fails")) ctx
                       end 
                 | Left err -> Left err

and predicate_read p g q l' l ctx psi i c2' =
  if (predicate_return p q ctx)
  then
    let ibeta = (List.assoc_opt g p) in
      match ibeta with
      | Some (IBeta beta) ->
      let c_1 =  CTrue in
        let c_2 = merge_cs c2' (CLeq (l', l))  in 
                      let c_3 =  CImpl (ctx.constr_env, c_2) in 
                        let c_4 = quantify_all_exist (ctx.evar_ctx @ psi ) c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
                          let elim_c_5 =  Exist_elim.elimt ctx c_5  
                            (fun cs' ->
                               cs'
                              ) in 
                            let w_c= WhyTrans.why3_translate(* _int *) elim_c_5(* c_5 *) in 
                            b_debug dp "b predicate_read  : @[  w_c: %a @]"  Why3.Pretty.print_term w_c;
                            WhySolver.post_st w_c 1
   | _ -> false
  
  else false  
and predicate_readB p g q l' l ctx psi i =
   if (predicate_return p q ctx)
   then
      let ibeta = (List.assoc_opt g p) in
      match ibeta with
      | Some (IBeta beta) ->
         let c_1 =  CNot (CBetaIn (l', beta ) ) in
        let c_2 = merge_cs c_1 (CLeq (l', l))  in 
                      let c_3 =  CImpl (ctx.constr_env, c_2) in 
                        let c_4 = quantify_all_exist (ctx.evar_ctx @ psi ) c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
                          b_debug dp "b predicate_read B c5: @[  c_5: %a @]"  Print.pp_cs c_5;
                            let w_c= WhyTrans.why3_translate_int c_5 in 
                            b_debug dp "b predicate_read B : @[  w_c: %a @]"  Why3.Pretty.print_term w_c;
                            WhySolver.post_st w_c 1
      | _ -> false
  
  else false  
  
           
and check_alloc (eP1: expr * expr) (eP2: expr * expr) (p:predicate) g (q:predicate) bty i (k:iterm)  =
  fun (ctx, k') -> 
    if (Unary.preselect_alloc p q g ctx) then 
       begin
    match bty with
    | BArray (g', n, bty_1) -> 
       if g = g' then
         
         if (predicate_AllTrue p g q ctx) then
           ( check_body (  (checkBType eP1 (BInt(n)) )  >> (checkBType eP2 bty_1) )  k ) (ctx,k')
         else 
           begin
         if (predicate_AllFalse p g q ctx) then
           ( check_body (  (checkBType eP1 (BInt(n)) )  >> (checkBType eP2 (BTyBox bty_1) ) )   k ) (ctx,k')
         else fail i (WrongBShape (bty_1, "b alloc 1 return type"))  (ctx,k')
           end
      else fail i (WrongBShape (bty_1, "b alloc 2 return type"))   (ctx,k')   
    | _ ->  fail i (WrongBShape (bty, " b alloc 3 return type")) (ctx,k')
      end
    else
      fail i (WrongBShape (bty, " b alloc 4 preselect fails")) (ctx,k')

(* and preselect_alloc (p: predicate) (q: predicate) (g: var_info) : bool =
    if ( List.mem_assoc g q ) && not (List.mem_assoc g p) && (List.length q = (List.length p) + 1) then
      List.for_all (fun (g,iarr) ->
           match List.assoc_opt g q with 
              | Some (iarr') -> true(* check_iarrays_eq iarr iarr' ctx *)
              | None -> false
        ) p
    else false *)
  
and predicate_AllTrue p g q ctx : bool =
    let beta = (List.assoc_opt g q) in
            match beta with
             | None -> false
             | Some (IBeta b) ->
  
          let c_3= CBetaEq (b ,BIO) in
          let c_4 = quantify_all_exist ctx.evar_ctx c_3 in 
                          let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
                            let w_c= WhyTrans.why3_translate_int c_5 in 
                           
                              WhySolver.post_st w_c 1


    (* let ibeta = (List.assoc_opt g q) in
     *   match ibeta with
     *   | Some (IBeta beta) ->
     *      let c_1 =  (CBetaIn (l', beta ) ) in
     *     let c_2 = merge_cs c_1 (CLeq (l', l))  in 
     *                   let c_3 =  CImpl (ctx.constr_env, c_2) in 
     *                     let c_4 = quantify_all_exist ctx.evar_ctx c_3 in 
     *                       let c_5 = quantify_all_universal ctx.ivar_ctx c_4 in
     *                         let w_c= WhyTrans.why3_translate_int c_5 in 
     *                         b_debug dp "b predicate_read  : @[  w_c: %a @]"  Why3.Pretty.print_term w_c;
     *                         WhySolver.post w_c 1 *)
 

and predicate_AllFalse p g q ctx = true
   

and check_fix (i: info) (vi_f : var_info) (vi_x : var_info) (eP: expr * expr) (bty : ty) =
  get_heur >>>= 
    fun heur ->
      let ch_heur_fix m ty1 ty2 k_fun = 
	if heur = NoChange then
	  begin
	    match ty1 with
	    | BTyList(n, alph, ty) ->
	       (* assume alpha = 0 *)
	       assume_size_eq IZero alph
		(check_body ((vi_f |:| bty) ((vi_x |:| (BTyList(n, IZero, ty)))
		 (check_no_change eP (checkBType eP ty2) >||> (checkBType eP ty2)))) k_fun)
	       >&&>
		 (* assume alpha >= 1 *)
		 assume_size_leq (ISucc IZero) alph m
				 
            | _ -> m
          end
        else m
      in
      match bty with
      | BTyArr(ty1, k_fun, ty2) ->
        let m = check_body ((vi_f |:| bty) ((vi_x |:| ty1) (checkBType eP ty2))) k_fun in
	ch_heur_fix m ty1 ty2 k_fun
      | BTyBox (BTyArr(ty1, k_fun, ty2)) ->
	 if is_equal_exp (fst eP) (snd eP) then
	    let with_no_cost m = fun(ctx, k) -> m (ctx, None) in
	    let ch_ctx = with_no_cost
			   (check_no_change_types (Fix(i, vi_f, vi_x, fst eP), snd eP)) in
	    let m = check_body ((vi_f |:| bty) 
				  ((vi_x |:| ty1) (ch_ctx  >&&> checkBType eP ty2))) k_fun in
	    ch_heur_fix m ty1 ty2 k_fun
	 else  fail i (WrongBShape (bty, "Boxed function types require identical expressions"))
    | _ ->  fail i (WrongBShape (bty, "fuction fix"))
    

and check_body (m: constr checker) (k_fun : iterm) : constr checker =
  fun(ctx, k) ->
    match k with
    | Some k -> 
      begin
        match m (ctx, Some k_fun) with
      | Right c ->  Right(CAnd(c, cost_cs ctx (IZero, k)))
      | Left err -> Left err
      end
    | None -> m (ctx, None)
    
and check_handle_unrel (m: constr checker) ePair bty : constr checker =
  fun(ctx, k) ->
    let mc = m(ctx, k) in 
    match mc with
    | Left err' when err'.v = Ty_error.SwitchPMatch -> 
      let uty1 = (bi_ty_proj true bty) in
      let uty2 = (bi_ty_proj false bty) in
      check_unrel (fst ePair) (snd ePair) uty1 uty2(ctx, k)
    | _ ->  mc

                  
and check_if (i : info) eP ePl ePr bty ePair =
 check_handle_unrel (inferBType eP  <->=
   (fun bty_g ->
      let pty = push_box bty_g in
      match pty with
      | BTyPrim BPrimBool -> (checkBType ePl bty) >> (checkBType ePr bty)
      | BTyUnrel _ -> 
        begin
          match bty with
          | BTyUnrel _ -> 
            (* Guard is unrelated, force switching to unary mode at top level *)
            fail i SwitchPMatch
          | _ -> fail i (WrongBShape (bty, "unrelated result"))
        end
      | _ -> fail i (WrongBShape (bty_g, "bool"))))
   ePair bty
   

and check_nil i bty =
  match bty with
  | BTyList(n, a, ty) -> check_size_leq IZero a (check_size_eq n IZero return_leaf_ch)
  | _ -> fail i (WrongBShape (bty, "list"))

and check_cons eP1 eP2 i bty =
  match bty with
  | BTyList(n, alph, ty) ->
    (* Introduce a new size variable and add it to the existential ctx*)
    let v = fresh_evar Size in
    let sz = IVar v in
    b_debug dp " ck cons :@\n@[ty is %a @]@." Print.pp_btype ty  ;
    (v |:::| Size) i
      (* Check that (sz + 1 = n) *)
      (check_size_eq n (ISucc sz)
         begin
           (*-- Case for boxed head *)
           ( 
            (checkBType eP1 (BTyBox ty)) >>
             (checkBType eP2 (BTyList(sz, alph, ty))))
           >||>
           (*-- Case for changeable head *)
           (* Introduce a new size variable and add it to the
              existential ctx *)
           (let v' = fresh_evar Size in
            let beta = IVar v' in
             ( 
            (v' |:::| Size) i
              (checkBType eP1 ty >>
               check_size_leq (ISucc beta) (alph)
                 (checkBType eP2 (BTyList(sz, beta, ty))))) )
         end
      )
  | _ ->  fail i (WrongBShape (bty, "list"))


and check_case_list i eP ePn x_h x_tl ePc bty =
b_debug dp "cklist: eP: %a, ePc: %a, bty : %a" Print.pp_expr (fst ePn) Print.pp_expr (fst ePc) Print.pp_btype bty ;
  inferBType eP <->=
  fun bty_g ->
    match bty_g

 with
    | BTyBox(BTyList (n, alph, tye)) 
    | BTyList (n, alph, tye) ->
      (* Nil case *)
      (assume_size_eq n IZero (checkBType ePn bty))
      >&&>
      (* Cons case *)
      (* Generate a fresh size variable *)
      let v = fresh_ivar Size in
      let sz = IVar v in
      (* Extend the index ctx with freshly gen. size*)
      (v |::| Size) i
        (* Assume that n = sz + 1*)
        (assume_size_eq n (ISucc sz)
           (* There are two cases depending on whether head can change *)
           (* Cons case1-- x_h : box tye, x_tl: L[sz+1, alph] *)
           begin 
             ( (x_h  |:| BTyBox tye)
                 ( (x_tl |:| BTyList(sz, alph, tye)) (checkBType ePc bty)))
             >&&>
             (* Cons case2-- x_h : tye, x_tl: L[sz+1, beta] where beta+1 = alph *)
             (
               let v' = fresh_ivar Size in
               let beta = IVar v' in
               (* Extend the index ctx with freshly gen. size*)
               ((v' |::| Size) i
                  (* Assume that alph = beta + 1*)
                  (assume_size_eq alph (ISucc beta)
                     ((x_h |:| tye)
                        (( x_tl |:| BTyList(sz, beta, tye))
                           (checkBType ePc bty)))))
             )
           end
        ) 
      
    | _ -> fail i (WrongBShape (bty_g, "list"))
  



and check_case_sum i eP x_l ePl x_r ePr  bty =
  inferBType eP <->=
  (fun bty_g ->
     match bty_g with
     | BTySum (tyl, tyr) -> 
       (x_l |:| tyl) (checkBType ePl bty) >&&>  (x_r |:| tyr) (checkBType ePr bty)
     | _ -> fail i (WrongBShape (bty, "sum"))
  )

and check_pack i eP bty =
  match bty with
  | BTyExists(x, s, ty) ->
    let v = fresh_evar s in
    let witness = IVar v in
    (v |:::| s) i (checkBType eP (bi_ty_subst x witness ty))
  | _ -> fail i (WrongBShape (bty, "existential"))

and check_unpack i eP1 vi_x eP2 bty =
  inferBType eP1 <->=
  (fun bty_x ->
    
     match push_box bty_x with
     | BTyExists(x, s, ty) ->
       (x |::| s) i
         ((vi_x |:| ty) (checkBType eP2 bty))
     | BTyUnrel(uty1, uty2) -> check_unrel (Unpack(i, fst eP1, vi_x, fst eP2)) (Unpack(i, snd eP1, vi_x, snd eP2)) uty1 uty2
     | _ -> fail i (WrongBShape (bty, "existential"))
      )
     
and check_clet i vi_x eP1 eP2 bty =
  inferBType eP1 <->=
  (fun csty ->
     match push_box csty with
     | BTyCs(cs, bty_x) ->
         (vi_x |:| bty_x) (checkBType eP2 bty) >>=
	  fun cs_b -> return_ch (CImpl(cs, cs_b))
     | _ -> fail i (WrongBShape (bty, "constrained")))

(* only checks if the expression has any dependencies to changeable
   input, cost restriction is checked later *)
and check_no_change_types (eP: expr * expr) : constr checker =
  fun(ctx, k) ->
    let i = (expInfo (fst eP)) in
    let free_vars = (exp_free_vars (fst eP)) in
    let check_context_stable = List.fold_left
        (fun acc x-> 
           (match (lookup_var x ctx) with
              None -> fail i (Internal ("variable " ^ x ^ " missing type"))
            | Some (v, g_tau) -> 
	      check_bsubtype i g_tau (BTyBox g_tau) >&&> acc)) (return_ch empty_constr) free_vars in
    check_context_stable(ctx, k)

and check_no_change (eP: expr * expr)  (m': constr checker)  : constr checker =
  if is_equal_exp (fst eP) (snd eP) then
    let m = check_no_change_types eP in
    let k' = fresh_evar Cost in 
    let with_no_cost m = fun(ctx, k) -> m (ctx, None) in
    (k' |:::| Cost) (NOCHANGE) (with_no_cost (m >&&> m'))
  else fail (expInfo (fst eP)) (Internal ("expressions are not the same "))


and check_unrel e1 e2 uty1 uty2 =
  fun(ctx, k) ->
    let u1ctx = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.var_ctx in
    let u2ctx = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.var_ctx in
     let u1ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.uvar_ctx in
    let u2ctx' = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.uvar_ctx in
    let u1 = union_ctx u1ctx u1ctx' in 
    let u2 = union_ctx u2ctx u2ctx' in 
    let lctx = (set_ctx u1 u1ctx' MaxEx ctx) in
    let rctx = (set_ctx u2 u2ctx' MinEx ctx) in
    let v' = fresh_evar Cost in
    let k' = IVar v' in
    let kl_ctx = Core.Option.value_map ~default:lctx ~f:(fun _ -> extend_e_var v'.v_name Cost lctx) k in
    let kr_ctx = Core.Option.value_map ~default:rctx ~f:(fun _ -> extend_e_var v'.v_name Cost rctx) k in
    let k1 = Core.Option.map ~f:(fun k -> IAdd(k, k')) k in
    let k2 = Core.Option.map ~f:(fun _ -> k') k in
    b_debug dp "SWITCH check unrel :@\n@[k1:%a + k2:%a @]@." Print.pp_cost k1 Print.pp_cost k2 ;
    begin
      match Unary.checkUType e1 uty1 (kl_ctx, k1) with
      | Right c1 -> b_debug dp "SWITCH check unrel2 :@\n@[c1:%a  @]@." Print.pp_cs c1  ;
         begin
           match Unary.checkUType e2 uty2 (kr_ctx, k2) with
           | Right c2 ->  b_debug dp "SWITCH check unrel3 :@\n@[ c2:%a @]@."  Print.pp_cs c2 ;
           Right (CExists(v', (expInfo e1),  Cost, merge_cs c1 c2))
           | Left err -> Left err
         end
      | Left err -> Left err
    end
       
and infer_and_check (i: info) (eP: expr * expr) (bty : ty) : constr checker =
  fun(ctx, k) ->
    match inferBType eP ctx with
    | Right (inf_bty, c, psi_ctx, k') ->
    b_debug dp "b infer_and_check :@\n@[infer_type is %a, expr is %a, checked type is %a, k' is %a, k is %a @]@." 
      Print.pp_btype inf_bty Print.pp_expr (fst eP) Print.pp_btype bty Print.pp_cost k' Print.pp_cost k; 
       begin
         match (check_bsubtype i inf_bty bty (extend_e_ctx psi_ctx ctx, None)) with
         | Right c' ->
            let cs = option_combine k' k (cost_cs ctx) |> Core.Option.value ~default:CTrue in
          Right (quantify_all_exist psi_ctx (merge_cs (merge_cs c c') cs))
       | Left err -> Left err
       end
    | Left err' -> Left err'

and union_ctx ctx1 ctx2 =
    List.map  (fun (v, uty) -> if (List.mem_assoc v ctx2) then (v, List.assoc v ctx2) else (v, uty) ) ctx1


let check_type ctx prgm1 prgm2 bty k =
  match checkBType (prgm1, prgm2) bty (ctx, k) with
  | Right c -> c
  | Left err -> typing_error_pp  err.i pp_tyerr err.v
 
