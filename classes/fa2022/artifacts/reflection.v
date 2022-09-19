Require Import Nat List.
Import ListNotations.

(*
 * TODO comment etc
 * TODO refer folks to the lecture note demo to build on that
 *)

(* --- TODO --- *)

Inductive Same_Length {T : Type} : list T -> list T -> Prop :=
| length_nil : Same_Length [] []
| length_cons :
    forall (hd1 hd2 : T) (tl1 tl2 : list T),
      Same_Length tl1 tl2 ->
      Same_Length (hd1 :: tl1) (hd2 :: tl2).

Fixpoint nat_to_zero_list (n : nat) : list nat :=
  match n with
  | O => []
  | S m => O :: nat_to_zero_list m
  end.

Fixpoint nat_to_one_list (n : nat) : list nat :=
  match n with
  | O => []
  | S m => 1 :: nat_to_one_list m
  end.

(*
 * TODO exercise: print and look at how big it is
 *)
Lemma same_length_lists_50:
  Same_Length (nat_to_zero_list 50) (nat_to_one_list 50).
Proof.
  repeat constructor.
Qed.

Print same_length_lists_50.

(*
 * TODO exercise --- how long does it take?
 *)
Lemma same_length_lists_1000:
  Same_Length (nat_to_zero_list 1000) (nat_to_one_list 1000).
Proof.
  time (repeat constructor).
Qed.

(*
 * I don't recommend printing ... crashed my CoqIDE
 *)

(* --- TODO --- *)

(*
 * TODO exercise
 *)
Fixpoint check_same_length {T : Type} (l1 l2 : list T) : option (Same_Length l1 l2) :=
  match l1, l2 with
  | [], [] => Some length_nil
  | hd1 :: tl1, hd2 :: tl2 =>
      match check_same_length tl1 tl2 with
      | Some p => Some (length_cons hd1 hd2 tl1 tl2 p)
      | None => None
      end
  | _, _ => None
  end.

(*
 * TODO define for you all
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
 * TODO explain, exercise
 *)
Lemma same_length_lists_50_reflective:
  Same_Length (nat_to_zero_list 50) (nat_to_one_list 50).
Proof.
  exact (optionOut (Same_Length (nat_to_zero_list 50) (nat_to_one_list 50)) (check_same_length (nat_to_zero_list 50) (nat_to_one_list 50))).
Qed.

Print same_length_lists_50_reflective.
Print same_length_lists_50.

(*
 * TODO exercise --- how long does it take? compare to other
 *)
Lemma same_length_lists_1000_reflective:
  Same_Length (nat_to_zero_list 1000) (nat_to_one_list 1000).
Proof.
  time (exact (optionOut (Same_Length (nat_to_zero_list 1000) (nat_to_one_list 1000)) (check_same_length (nat_to_zero_list 1000) (nat_to_one_list 1000)))).
Qed.

(*
 * Note how small this is!
 *)
Print same_length_lists_1000_reflective.

(* --- TODO --- *)

(*
 * TODO exercise, try to use this to prove bad thing,
 * what happens? Why? What could you prove with this tactic instead?
 *)
Lemma same_length_bad : Same_Length (nat_to_zero_list 50) (nat_to_one_list 1000).
Proof.
  (*exact (optionOut (Same_Length (nat_to_zero_list 50) (nat_to_one_list 1000)) (check_same_length (nat_to_zero_list 50) (nat_to_one_list 1000))).*)
Abort.

(* --- TODO --- *)

(*
 * TODO explain, exercise. proofs below should go through quickly if this is good.
 *)
Ltac prove_same_length :=
  match goal with
  | [ |- Same_Length ?l1 ?l2] => exact (optionOut (Same_Length l1 l2) (check_same_length l1 l2))
  end.

Lemma same_length_lists_50_ltac:
  Same_Length (nat_to_zero_list 50) (nat_to_one_list 50).
Proof.
  prove_same_length.
Qed.

Lemma same_length_lists_1000_ltac:
  Same_Length (nat_to_zero_list 1000) (nat_to_one_list 1000).
Proof.
  prove_same_length.
Qed.

Lemma same_length_lists_5000_ltac:
  Same_Length (nat_to_zero_list 5000) (nat_to_one_list 5000).
Proof.
  prove_same_length.
Qed.

(* --- TODO --- *)

Definition check_same_length_is_some {T : Type} (l1 l2 : list T) :=
  exists (H : Same_Length l1 l2), check_same_length l1 l2 = Some H.

(*
 * TODO exercise etc
 *)
Theorem check_same_length_OK:
  forall {T : Type} (l1 l2 : list T),
    Same_Length l1 l2 <-> check_same_length_is_some l1 l2.
Proof.
  intros l1 l2. split.
  - intros H. induction H.
    + econstructor. reflexivity.
    + destruct IHSame_Length. unfold check_same_length_is_some.
      simpl. rewrite H0.
      econstructor. eauto.
  - intros H. destruct H. apply x.
Qed.

(*
 * TODO bonus exercise etc
 *)
Theorem check_same_length_OK_alt:
  forall {T : Type} (l1 l2 : list T),
    length l1 = length l2 <-> check_same_length_is_some l1 l2.
Proof.
  intros T. induction l1, l2; split; intros H.
  - econstructor. reflexivity.
  - reflexivity.
  - inversion H.
  - inversion H. inversion x.
  - inversion H.
  - inversion H. inversion x.
  - simpl in *. unfold check_same_length_is_some.
    simpl. inversion H. destruct (IHl1 l2). specialize (H0 H1).
    unfold check_same_length_is_some in H0.
    destruct H0. rewrite H0.
    econstructor. eauto.
  - destruct (IHl1 l2). destruct H. simpl.
    f_equal. apply H1. rewrite <- check_same_length_OK.
    inversion x. apply H3.
Qed.

(* --- TODO --- *)

(*
 * TODO discussion question etc
 *)
