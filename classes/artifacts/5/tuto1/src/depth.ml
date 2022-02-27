(* TODO explain *)

let rec find_depth env sigma trm =
  match EConstr.kind sigma trm with
  | Constr.Lambda (n, t, b) ->
     let env_b = Termutils.push_local (n, t) env in
     let sigma_b, depth_b = find_depth env_b sigma (Termutils.shift b) in
     sigma_b, 1 + depth_b
  | Constr.Prod (n, t, b) ->
     let env_b = Termutils.push_local (n, t) env in
     let sigma_b, depth_b = find_depth env_b sigma (Termutils.shift b) in
     sigma_b, 1 + depth_b
  | _ ->
     sigma, 0
