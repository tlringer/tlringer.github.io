let __coq_plugin_name = "tuto1_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_tuto1.mlg"
 

(*
  This is a modified version of the Coq plugin tutorial.
  TODO explain, explain class format, explain utils file
 *)
open Pp
open Stdarg
open Termutils
open Exercise



let () = Vernacextend.vernac_extend ~command:"MyDefine" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MyDefine", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body i e
         () = Vernacextend.VtDefault (fun () -> 
# 39 "src/g_tuto1.mlg"
    
     let sigma, env = global_env () in
     let sigma, t = internalize env e sigma in
     define i t sigma
   
              ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Count" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Count", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body e1 e2
         () = Vernacextend.VtDefault (fun () -> 
# 53 "src/g_tuto1.mlg"
    
     let sigma, env = global_env () in
     let sigma, t1 = internalize env e1 sigma in
     let sigma, t2 = internalize env e2 sigma in
     let sigma, count = count env t1 t2 sigma in
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
         (let coqpp_body src_es dst_es e i
         () = Vernacextend.VtDefault (fun () -> 
# 70 "src/g_tuto1.mlg"
    
     let sigma, env = global_env () in
     let sigma, srcs = map_state (internalize env) src_es sigma in
     let sigma, dsts = map_state (internalize env) dst_es sigma in
     let sigma, trm = internalize env e sigma in
     let sigma, subbed =
       fold_left_state
         (fun subbed (src, dst) -> sub env (src, dst) subbed)
         trm
         (List.combine srcs dsts)
         sigma
     in Termutils.define i subbed sigma
   
              ) in fun src_es
         dst_es e i ?loc ~atts () -> coqpp_body src_es dst_es e i
         (Attributes.unsupported_attributes atts)), None))]

