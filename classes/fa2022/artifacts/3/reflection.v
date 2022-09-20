Require Import Nat List.
Import ListNotations.

(*
 * This is an exercise on proof by reflection.
 * As always, it's about the journey, not the destination.
 * So there will be a discussion question at the bottom of the
 * file---you will be graded on answering that in the class
 * forum, and not your finished proofs. So don't worry
 * too much if you get stuck! But I'll be around to help.
 *
 * IMPORTANT NOTE: Throughout this exercise, you may find it
 * useful to look at the demo file from class on Tuesday:
 * https://dependenttyp.es/classes/fa2022/readings/reflectionnotes.v
 * It is totally fine to do this. The goal isn't to memorize
 * how to write these proofs, but rather to adapt this style
 * of automation to a different proof so you get a feel for
 * what it's like. Hope that helps!
 *)

(* --- Part 1: naive tactic proofs --- *)

(*
 * In this file, we're going to show that some very large
 * lists have the same length. It's a bit silly, but we'll
 * do so using this inductive relation, which is inhabited
 * whenever two lists are the same length:
 *)
Inductive Same_Length {T : Type} : list T -> list T -> Prop :=
| length_nil : Same_Length [] []
| length_cons :
    forall (hd1 hd2 : T) (tl1 tl2 : list T),
      Same_Length tl1 tl2 ->
      Same_Length (hd1 :: tl1) (hd2 :: tl2).

(*
 * Informally, note that for lists l1 and l2, we can construct a
 * term of type Same_Length l1 l2 if and only if l1 and l2 have
 * the same length: If l1 or l2 is nil, we construct this by the
 * length_nil constructor. If l1 and l2 are both not nil, and
 * the tails of l1 and l2 are the same length, then we can
 * construct this with the length_cons constructor. In all
 * other cases, we cannot construct an element of this type.
 *
 * The functions below let us construct very large lists easily.
 * The first gives us a list of length n that is all zeros:
 *)
Fixpoint nat_to_zero_list (n : nat) : list nat :=
  match n with
  | O => []
  | S m => O :: nat_to_zero_list m
  end.

(*
 * The second gives us a list of length n that is all ones:
 *)
Fixpoint nat_to_one_list (n : nat) : list nat :=
  match n with
  | O => []
  | S m => 1 :: nat_to_one_list m
  end.

(*
 * EXERCISE 1: I've written a proof below that shows that
 * two particular lists of length 50 are equal to each other.
 * Print the proof and look at it. Why is it so big?
 * Discuss with your group. 
 *)
Lemma same_length_lists_50:
  Same_Length (nat_to_zero_list 50) (nat_to_one_list 50).
Proof.
  repeat constructor.
Qed.

Print same_length_lists_50.

(*
 * EXERCISE 2: I've written another inefficient proof, this
 * time about lists of length 1000. The "time" tactical here
 * reports how long this proof takes. How long does it take?
 * Why do you think it takes so long? (I strongly recommend 
 * against printing this proof. Doing so crashed CoqIDE for me.)
 *)
Lemma same_length_lists_1000:
  Same_Length (nat_to_zero_list 1000) (nat_to_one_list 1000).
Proof.
  time (repeat constructor).
Qed.

(* --- Part 2: defining a decision procedure --- *)

(*
 * Next, we will write the same proofs by reflection, using
 * a decision procedure that checks whether two lists are
 * the same length.
 *
 * EXERCISE 3: Fill in the decision procedure below.
 * If you are successful, the proofs of both
 * same_length_lists_50_reflective and 
 * same_length_lists_1000_reflective below
 * should go through, and they should do so efficiently.
 *)
Fixpoint check_same_length {T : Type} (l1 l2 : list T) : option (Same_Length l1 l2) :=
  match l1, l2 with
  | [], [] => None (* replace with your code *)
  | hd1 :: tl1, hd2 :: tl2 => None (* replace with your code *)
  | _, _ => None
  end.

(*
 * I define these for you---note that, as in the demo we
 * saw on Tuesday, these let us apply our decision procedure
 * easily even though our decision procedure is partial
 * (it returns an optional proof that the lists are the same length,
 * and that proof is None when the lists are not the same length).
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
 * This proof should go through efficiently if your decision
 * procedure is correct:
 *)
Lemma same_length_lists_50_reflective:
  Same_Length (nat_to_zero_list 50) (nat_to_one_list 50).
Proof.
  exact (optionOut (Same_Length (nat_to_zero_list 50) (nat_to_one_list 50)) (check_same_length (nat_to_zero_list 50) (nat_to_one_list 50))).
Qed.

(*
 * This should be small if your decision procedure is correct:
 *)
Print same_length_lists_50_reflective.

(*
 * EXERCISE 4: How long does this proof by reflection take?
 * How much faster is it than the naive tactic proof of the
 * same theorem?
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

(*
 * EXERCISE 5: What happens if you try to use the same tactic
 * to prove something unprovable? Why? What theorem could you 
 * prove with this tactic instead?
 *)
Lemma same_length_bad : Same_Length (nat_to_zero_list 50) (nat_to_one_list 1000).
Proof.
  (*exact (optionOut (Same_Length (nat_to_zero_list 50) (nat_to_one_list 1000)) (check_same_length (nat_to_zero_list 50) (nat_to_one_list 1000))).*)
Abort.

(* --- Part 3: reflective tactics --- *)

(*
 * Now you can wrap all of this inside of a cute tactic, which
 * we'll call prove_same_length. You again may wish to refer to
 * the demo from Tuesday for this.
 *
 * EXERCISE 6: Implement the tactic prove_same_length, which
 * should prove the below proofs efficiently if the tactic
 * is correct.
 *)
Ltac prove_same_length := idtac. (* replace with your code *)

(*
 * These should all go through efficiently now:
 *)
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

(* --- Part 4: proving your automation correct --- *)

(*
 * EXERCISE 7: Prove check_same_length_OK below, which shows
 * that your check_same_length decision procedure returns
 * some proof that two lists are the same length if and only if
 * they're actually the same length.
 *
 * It will probably help a lot to look at the proof from the
 * demo in class. Tactics I found helpful (YMMV):
 *   `intros` (introduction)
 *   `split` (split P <-> Q into P -> Q and Q -> P)
 *   `induction` (note that you can induct not just over lists,
 *                but also over all proofs of Same_Length l1 l2
 *                for any two lists l1 and l2, and this may be
 *                easier for this proof)
 *   `econstructor` (apply some constructor, but choose it for me)
 *   `reflexivity`
 *   `eauto` (like auto, but also infer some arguments I don't
 *            feel like figuring out myself)
 *   `destruct` (like induction, but don't bother defining an
 *               inductive hypothesis)
 *   `unfold` (delta-reduce or unfold constants)
 *   `rewrite` (rewrite by equalities, like subst in Agda)
 *   `apply` (apply a hypothesis or lemma to some arguments)
 *
 * It's OK if this proof is hard. If it is, I recommend stepping
 * through the corresponding proof about isEven in the demo from
 * class on Tuesday (linked at the top of this file), and making
 * sure you understand each step.
 *)

Definition check_same_length_is_some {T : Type} (l1 l2 : list T) :=
  exists (H : Same_Length l1 l2), check_same_length l1 l2 = Some H.

Theorem check_same_length_OK:
  forall {T : Type} (l1 l2 : list T),
    Same_Length l1 l2 <-> check_same_length_is_some l1 l2.
Proof.
  (* your proof here *)
Abort. (* <- change to Qed when done *)

(*
 * BONUS EXERCISE: If you have extra time, prove that this is
 * not only correct, but also respects the actual length function.
 * You may prove this however you like.
 *)
Theorem check_same_length_OK_alt:
  forall {T : Type} (l1 l2 : list T),
    length l1 = length l2 <-> check_same_length_is_some l1 l2.
Proof.
  (* your proof here *)
Abort. (* <- change to Qed when done *)

(* --- Discussion --- *)

(*
 * Answer in the class forum, exactly one answer per group,
 * listing the names of everyone in your group as always:
 * Think back to the three different ways you've written
 * proofs so far in this class: by constructing proof terms
 * directly (Agda, Artifact 1), by using tactics (Coq, Artifact 2),
 * and by reflection (Coq, Artifact 3). When do you think you'd
 * use each one over the others, if ever? And why (even if never)?
 *)
