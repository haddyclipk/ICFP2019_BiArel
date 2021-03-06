open Syntax
open IndexSyntax
open Constr

(* Context management *)
(* ---------------------------------------------------------------------- *)
type heurMode = NoChange | Usual

type costMode = NoCost | WithCost

(* Contexts of type 'a *)
type 'a ctx = (var_info * 'a) list

(* Unary/Binary context *)
type 'a context =
    {
      var_ctx   : 'a ctx;
      uvar_ctx : 'a ctx ;
      ivar_ctx  : sort ctx;
      evar_ctx  : sort ctx;
      exec_mode : mode;
      heur_mode : heurMode;
      cost_mode : costMode;
      lvar_ctx  : var_info list;
      constr_env :  constr
    }

let length ctx = List.length ctx

let empty_context = { var_ctx = []; uvar_ctx =[] ; evar_ctx = []; ivar_ctx = []; exec_mode = MaxEx; heur_mode = Usual; cost_mode = WithCost; lvar_ctx=[]; constr_env= CTrue}

(* Return a binding if it exists. Let the caller handle the error *)
let rec slookup id ctx =
  match ctx with
      []                -> None
    | (var, value) :: l ->
      if var.v_name = id then
        Some (var, value)
      else
        slookup id l

let lookup_var id ctx =
  slookup id ctx.var_ctx

let lookup_ivar id ctx =
  slookup id ctx.ivar_ctx

let lookup_evar id ctx =
  slookup id ctx.evar_ctx

let rec lookup_lvar id ctx = 
    match ctx with
        [] -> None
      | v::l -> 
        if(v.v_name = id) then 
          Some v
        else
          lookup_lvar id l 

 

(* Extend the context with a new variable binding. *)
let extend_var id s ctx =
  let n_var = {
    v_name  = id;
    v_type  = BiVar;
  } in
  {ctx with var_ctx   = (n_var, s) :: ctx.var_ctx }

let extend_uvar id s ctx =
  let n_var = {
    v_name  = id;
    v_type  = BiVar;
  } in
  {ctx with uvar_ctx   = (n_var, s) :: ctx.uvar_ctx }

  (*for location environment *)
let extend_l_var id ctx =
  let n_var = {
    v_name= id;
    v_type= BiLVar;
  } in
   {ctx with lvar_ctx = (n_var) :: ctx.lvar_ctx }

(* Extend the index context with a new binding. Return the new context. *)
let extend_i_var id s ctx =
  let n_var = {
    v_name  = id;
    v_type  = BiIVar;
  } in
  { ctx with ivar_ctx = (n_var, s) :: ctx.ivar_ctx }

(* Extend the existential context with a new binding. Return the new context. *)
let extend_e_var id s ctx =
  let n_var = {
    v_name  = id;
    v_type  = BiEVar s; 
  } in
  { ctx with evar_ctx = (n_var, s) :: ctx.evar_ctx }

(* Extend the existential context with a list of bindings. Return the new context. *)
let extend_e_ctx psi ctx =
  List.fold_left (fun  ctx' (vi,s) -> extend_e_var vi.v_name s ctx') ctx psi

    
let set_exec_mode mu ctx = 
  { ctx with exec_mode = mu }

let set_heur_mode mo ctx = 
  { ctx with heur_mode = mo }

(* let set_uctx u_ctx mu ctx = *)
(*   { ctx with exec_mode = mu } *)

let set_ctx u_ctx u_ctx' mu ctx =
  {
    var_ctx   = u_ctx;
    uvar_ctx = u_ctx';
    ivar_ctx = ctx.ivar_ctx;
    evar_ctx = ctx.evar_ctx;
    exec_mode = mu;
    heur_mode = ctx.heur_mode;
    cost_mode = ctx.cost_mode;
    lvar_ctx =  ctx.lvar_ctx;
    constr_env =  ctx.constr_env;
  }



let set_cost_mode mo ctx = 
  { ctx with cost_mode = mo }
