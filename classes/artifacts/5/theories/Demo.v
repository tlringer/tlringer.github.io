From Tuto1 Require Import Loader.

(*** Defining terms ***)

MyDefine n := 1.
Print n.

MyDefine f := (fun (x : Type) => x).
Print f.

MyDefine definition := 5.
Print definition.

MyDefine foo := (fun (T : Type) => forall (P : T -> Type) (t : T), P t).
Print foo.

(*** Reasoning about terms ***)

Count nat in (foo nat). (* 1 *)
Count nat in (fun (n : nat) => n). (* 1 *)

Definition my_nat := nat.
Count my_nat in (foo nat). (* 1 *)

Count S in 8. (* 8 *)
Count (fun (n : nat) => 1 + n) in 8. (* 8 *)
(* TODO more tests *)

(*** Substitution ***)
Sub O S with (@nil nat) (cons 1) in 4 as list_4.
Print list_4. (* (1 :: 1 :: 1 :: nil) *)

Require Import Coq.NArith.BinNatDef Coq.NArith.BinNat.
Sub O S with N.zero N.succ in 256 as two_fifty_six_binary.
Eval compute in two_fifty_six_binary.

Sub nat nat_rec O S with N.t N.peano_rec N.zero N.succ in
  (fun (n m : nat) =>
     nat_rec
       (fun _ => nat -> nat)
       (fun m => m)
       (fun p add_p m => S (add_p m))
       n
       m)
   as add_bin.

Print Nat.add. 
Print add_bin.

Eval compute in (add_bin two_fifty_six_binary two_fifty_six_binary).


