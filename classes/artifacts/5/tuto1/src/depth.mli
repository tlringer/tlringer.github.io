(* TODO explain *)

val find_depth :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  Evd.evar_map * int
