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

(* TODO note can assume no match statements, fixpoints, etc etc etc *)
(* TODO note constants etc limitatoins *)
(* TODO add more tests that are useful *)
Arity n. (* 0 *)
Arity f. (* 0 *)
Arity definition. (* 0 *)
Arity foo. (* 0 *)
Arity (foo nat). (* 0 *)
Arity (fun (n : nat) => n). (* 1 *)
Arity (fun (T : Type) (P : T -> Type) => forall (t : T), P t). (* 3 *)

Nargs (foo nat). (* 1 *)
Nargs (fun (x y : nat) => x + y). (* 0 *)
Nargs ((fun (x y : nat) => x + y) 1). (* 1 *)
Nargs ((fun (x y : nat) => x + y) 1 3). (* 2 *)
Nargs (((fun (x y : nat) => x + y) 1) 3). (* 2 *)

Count nat in body (foo nat). (* 1 *)
Count nat in body (fun (n : nat) => n). (* 0 *)

Definition my_nat := nat.
Count my_nat in body (foo nat). (* 1 *)

Count S in body 8. (* 8 *)
Count (fun (n : nat) => 1 + n) in body 8. (* 8 *)
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


