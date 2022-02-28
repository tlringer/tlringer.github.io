let __coq_plugin_name = "tuto1_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_tuto1.mlg"
 

(*
  This is a modified version of the Coq plugin tutorial.
  TODO explain, explain class format, explain utils file
 *)
open Pp
open Stdarg
open Exercise



let () = Vernacextend.vernac_extend ~command:"MyDefine" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MyDefine", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body i e
         () = Vernacextend.VtDefault (fun () -> 
# 38 "src/g_tuto1.mlg"
    
     let (sigma, env) = Termutils.global_env () in
     let (sigma, t) = Termutils.internalize env e sigma in
     Termutils.define i t sigma
   
              ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Arity" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Arity", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.VtDefault (fun () -> 
                                                                
# 56 "src/g_tuto1.mlg"
    
     let (sigma, env) = Termutils.global_env () in
     let (sigma, t) = Termutils.internalize env e sigma in
     let (sigma, arity) = arity t sigma in
     Feedback.msg_notice (strbrk (string_of_int arity))
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Nargs" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Nargs", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.VtDefault (fun () -> 
                                                                
# 71 "src/g_tuto1.mlg"
    
     let (sigma, env) = Termutils.global_env () in
     let (sigma, t) = Termutils.internalize env e sigma in
     let (sigma, nargs) = nargs t sigma in
     Feedback.msg_notice (strbrk (string_of_int nargs))
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Count" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Count", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyTerminal ("body", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body e1 e2
         () = Vernacextend.VtDefault (fun () -> 
# 84 "src/g_tuto1.mlg"
    
     let (sigma, env) = Termutils.global_env () in
     let (sigma, t1) = Termutils.internalize env e1 sigma in
     let (sigma, t2) = Termutils.internalize env e2 sigma in
     let (sigma, count) = count_in_body env t1 t2 sigma in
     Feedback.msg_notice (strbrk (string_of_int count))
   
              ) in fun e1
         e2 ?loc ~atts () -> coqpp_body e1 e2
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Sub" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Sub", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil)))))))), 
         (let coqpp_body e1s e2s e3 i
         () = Vernacextend.VtDefault (fun () -> 
# 100 "src/g_tuto1.mlg"
    
     let (sigma, env) = Termutils.global_env () in
     let (sigma, t1s) = Termutils.map_state (Termutils.internalize env) e1s sigma in
     let (sigma, t2s) = Termutils.map_state (Termutils.internalize env) e2s sigma in
     let (sigma, t3) = Termutils.internalize env e3 sigma in
     let (sigma, subbed) =
       Termutils.fold_left_state
         (fun subbed (t1, t2) -> sub_in env (t1, t2) subbed)
         t3
         (List.combine t1s t2s)
         sigma
     in Termutils.define i subbed sigma
   
              ) in fun e1s
         e2s e3 i ?loc ~atts () -> coqpp_body e1s e2s e3 i
         (Attributes.unsupported_attributes atts)), None))]

