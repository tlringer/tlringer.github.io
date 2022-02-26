(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

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

(* TODO explain *)
let type_check env sigma trm =
  Typing.type_of env sigma trm
