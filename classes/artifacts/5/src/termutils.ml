(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

type 'a state = Evd.evar_map * 'a

let ret (a : 'a) = fun (sigma : Evd.evar_map) -> sigma, a
let bind f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma) 
                                               
(* TODO explain *)
let global_state () =
  let env = Global.env () in
  Evd.from_env env, env

(* TODO explain *)
let print env trm sigma =
  Printer.pr_econstr_env env sigma trm

(* TODO explain *)
let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

(* TODO explain, note highly simplified *)
let define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  ignore (Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma)

(* TODO explain *)
let equal env trm1 trm2 sigma =
  Reductionops.infer_conv env sigma trm1 trm2

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env
  
(* TODO explain, clean *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* TODO explain, clean *)
let map_state f args sigma =
  let sigma, fargs =
    fold_left_state
      (fun bs a sigma ->
        let sigma, b = f a sigma in
        sigma, b :: bs)
      []
      args
      sigma
  in sigma, List.rev fargs

(* TODO explain, clean *)
let fold_args f b args sigma =
  fold_left_state f b (Array.to_list args) sigma

(* TODO explain, clean, change type sig to use args only *)
let map_args f args =
  bind
    (map_state f (Array.to_list args))
    (fun fargs -> ret (Array.of_list fargs))
