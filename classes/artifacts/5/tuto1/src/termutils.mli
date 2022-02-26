(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

(* TODO explain *)
val internalize : Constrexpr.constr_expr -> Evd.evar_map * EConstr.t

(* TODO explain *)
val print : EConstr.t -> Pp.t

(* TODO explain *)
val define : Names.Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
