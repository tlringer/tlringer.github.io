(* TODO explain, rename to make it the right thing, fix the name elsewhere including in comments at top level. also note limitations (constants, reduction), make bonus problems *)

let rec arity trm sigma =
  match EConstr.kind sigma trm with
  | Constr.Lambda (n, t, b) ->
     let sigma_b, arity_b = arity b sigma in
     sigma_b, 1 + arity_b
  | Constr.Prod (n, t, b) ->
     let sigma_b, arity_b = arity b sigma in
     sigma_b, 1 + arity_b
  | _ ->
     sigma, 0

(* TODO call in caller, explain, move first, etc etc, mention limitations, etc etc *)
let rec nargs trm sigma =
  match EConstr.kind sigma trm with
  | Constr.App (f, args) ->
     let (sigma_f, nargs_f) = nargs f sigma in
     sigma_f, nargs_f + Array.length args  
  | _ ->
     sigma, 0
     
    
(* TODO call in caller etc etc, extend w/ more of AST or say OK to ignore other AST parts *)
let rec count_in_body env trm1 trm2 sigma =
  let sigma_opt = Termutils.equal env sigma trm1 trm2 in
  if Option.has_some sigma_opt then
    Option.get sigma_opt, 1
  else
    match EConstr.kind sigma trm2 with
    | Constr.Lambda (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       count_in_body env_b trm1 b sigma
    | Constr.Prod (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       count_in_body env_b trm1 b sigma
    | Constr.App (f, args) ->
       let sigma_f, occs_f = count_in_body env trm1 f sigma in
       Termutils.fold_args
         (fun occs arg sigma ->
           let sigma, occs_arg = count_in_body env trm1 arg sigma in
           sigma, occs_arg + occs)
         occs_f
         args
         sigma_f
    | _ ->
       sigma, 0

(* TODO move etc, same caveats as above *)
let rec sub_in_body env trm1 trm2 sigma =
  let sigma_opt = Termutils.equal env sigma trm1 trm2 in
  if Option.has_some sigma_opt then
    Option.get sigma_opt, trm1
  else
    match EConstr.kind sigma trm2 with
    | Constr.Lambda (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       sub_in_body env_b trm1 b sigma
    | Constr.Prod (n, t, b) ->
       let env_b = Termutils.push_local (n, t) env in
       sub_in_body env_b trm1 b sigma
    | Constr.App (f, args) ->
       let sigma_f, occs_f = sub_in_body env trm1 f sigma in
       Termutils.fold_args
         (fun subbed arg sigma ->
           let sigma, occs_arg = sub_in_body env trm1 arg sigma in
           sigma, occs_arg + occs)
         occs_f
         args
         sigma_f
    | _ ->
       sigma, trm2
