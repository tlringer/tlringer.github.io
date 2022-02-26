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
