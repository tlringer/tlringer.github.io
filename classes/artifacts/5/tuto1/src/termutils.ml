(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

open Declarations

(* TODO explain *)
let global_state () =
  let env = Global.env () in
  Evd.from_env env, env

(* TODO explain *)
let print env sigma trm =
  Printer.pr_econstr_env env sigma trm

(* TODO explain *)
let internalize env sigma trm =
  Constrintern.interp_constr_evars env sigma trm

(* TODO explain, note highly simplified *)
let define name sigma body =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma

(* Lookup a definition *)
let lookup_definition env sigma trm =
  match EConstr.kind sigma trm with
  | Constr.Const (c, u) ->
     let const = Environ.lookup_constant c env in
     let c_body = const.const_body in
     (match c_body with
      | Def cs -> sigma, EConstr.of_constr cs
      | OpaqueDef o -> failwith "term is opaque"
      | _ -> failwith "an axiom has no definition")
  | Constr.Ind _ -> sigma, trm
  | _ -> failwith "not a definition"

(* TODO explain *)
let type_check env sigma trm =
  Typing.type_of env sigma trm

(* TODO explain *)
let equal env sigma trm1 trm2 =
  Reductionops.infer_conv env sigma trm1 trm2

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* TODO explain, delete if unused *)
let shift trm =
  EConstr.of_constr (Constr.lift 1 (EConstr.Unsafe.to_constr trm))
  
(* TODO explain, clean *)
let fold_left_state (f : 'b -> 'a -> Evd.evar_map -> Evd.evar_map * 'b) (b : 'b) (l : 'a list) (sigma : Evd.evar_map) : Evd.evar_map * 'b =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l
 
(* TODO explain, clean *)
let fold_args (f : 'b -> 'a -> Evd.evar_map -> Evd.evar_map * 'b) (b : 'b) (args : 'a array) (sigma : Evd.evar_map) : Evd.evar_map * 'b =
  fold_left_state f b (Array.to_list args) sigma

(* TODO explain, clean, change type sig to use args only *)
let map_args (f : 'a -> Evd.evar_map -> Evd.evar_map * 'b) (args : 'a array) (sigma : Evd.evar_map) : Evd.evar_map * 'b array =
  let sigma, fargs =
    fold_args
      (fun bs a sigma ->
        let sigma, b = f a sigma in
        sigma, b :: bs)
      []
      args
      sigma
  in sigma, Array.of_list (List.rev fargs)
