Require Import Nat Arith.

(* --- Demo 1: Functions --- *)

(*
 * Consider the factorial function in Coq:
 *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => (S m) * (factorial m)
  end.

(*
 * Guess how these behave:
 *)
(*Eval compute in (factorial O).
Eval compute in (factorial 3).
Eval compute in (factorial 5).
Eval compute in (factorial 9).*)

(* --- Demo 2: Proofs --- *)

(*
 * Courtesy of Adam Chlipala in CPDT, adapted a bit to simplify
 *)

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Lemma even_256 : isEven 256.
Proof.
  repeat constructor.
Qed.

Print even_256. (* <- huge *)

(*
 * Let us instead define an evenness checker:
 *)
Fixpoint check_even (n : nat) : option (isEven n) :=
  match n with
  | O => Some Even_O
  | 1 => None
  | S (S m) =>
      match check_even m with
      | Some p => Some (Even_SS m p)
      | _ => None
      end
  end.

(*
 * Since our evenness checker is partial (it returns an option,
 * which is None when n is odd, or otherwise a proof of isEven n),
 * we need a way to get out of the option type when we do have
 * a proof. So we define some machinery for that:
 *)
Definition optionOutType (P : Prop) (o : option P) :=
  match o with
  | Some _ => P
  | _ => True
  end.

Definition optionOut (P : Prop) (o : option P) : optionOutType P o :=
  match o with
  | Some pf => pf
  | _ => I
  end.

(*
 * Now we have a much more efficient proof---one by reflection.
 * All it does is call our partial evenness checker, which
 * itself is a function that produces a proof. Then it projects
 * the result out of the option type so we get a proof.
 *)
Lemma even_256_reflective : isEven 256.
Proof.
  exact (optionOut (isEven 256) (check_even 256)).
Qed.

(*
 * Note how small this is!
 *)
Print even_256_reflective.
Print even_256.

(*
 * We can use this to prove any even number is even. But
 * we can't use this to prove odd numbers are even.
 * What happens if we do?
 *)
Lemma even_257_reflective : isEven 257.
Proof.
  (*exact (optionOut (isEven 257) (check_even 257))).*)
Abort.

(*
 * This does prove something. But it proves True, which is
 * trivial and always provable.
 *)
Lemma even_257_reflective : True.
Proof.
  exact (optionOut (isEven 257) (check_even 257)).
Qed.

(* --- Demo 3: Verified reflective tactics --- *)

Definition check_even_is_some (n : nat) :=
  exists (H : isEven n), check_even n = Some H.

Theorem check_even_OK:
  forall (n : nat), isEven n <-> check_even_is_some n.
Proof.
  intros n. split.
  - (* check_even is complete for even numbers: *)
    intros H. induction H.
    + econstructor. reflexivity.
    + destruct IHisEven. unfold check_even_is_some.
      simpl. rewrite H0.
      econstructor. eauto.
  - (* check_even is sound: *)
    intros H. destruct H. apply x.
Qed.

Ltac prove_even_reflective :=
  match goal with
  | [ |- isEven ?N] => exact (optionOut (isEven N) (check_even N))
  end.

Lemma even_256_reflective_ltac : isEven 256.
Proof.
  prove_even_reflective.
Qed.


