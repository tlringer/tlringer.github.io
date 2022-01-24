From iris.proofmode Require Import tactics.

(*
 * In this exercise, you will work in groups of 4 to implement a new tactic inside of
 * Iris proof mode. It may help to look at the paper for details of how tactics are
 * implemented, and it may help to look at other tactic implementions inside of the
 * Iris source code. If you have Coq experience, please join a group of people who
 * do not have Coq experience outside of this class.
 *
 * This exercise comes from Robbert Krebbers. Only the discussion questions and comments
 * are mine. Likewise, this skeleton file is based on a solution he shared publicly,
 * which I'm happy to share after class. But as usual, you will be graded not on your
 * implementation, but on the discussion questions at the end. These questions will
 * be easier, not harder, if you really try to implement this yourself.
 *
 * TODO note about simpler version etc, how the real version has extra complexities
 *
 * OK, let's get started!
 *)

(*
 * The tactic you will implement is called "iApply ... in", which is a real user
 * request in Iris proof mode. It's based on "apply ... in" from vanilla Coq.
 * That is, in Coq, we have the normal "apply" tactic, which applies a hypothesis to
 * refine a goal:
 *)
Lemma show_apply (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H1 H2 H3. (* goal : R *)
  apply H2. (* goal : Q *)
  apply H1. (* goal : P *)
  exact H3. (* no more goals *)
Qed.

(*
 * Well, in Coq, we also have "apply ... in", which applies hypotheses inside of
 * other hypotheses, to refine those hypotheses rather than the goal:
 *)
Lemma show_apply_in (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H1 H2 H3. (* H3 : P *)
  apply H1 in H3. (* H3 : Q *)
  apply H2 in H3. (* H3 : R *)
  exact H3. (* no more goals *)
Qed.

(*
 * Iris Proof Mode gives you an experience almost exactly like using Coq,
 * even though you're in a logic that can handle reasoning about concurrency.
 * Iris has "iApply" and "iExact" where Coq has "apply" and "exact":
 *)
Lemma show_iApply {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3". (* goal : R *)
  iApply "H2". (* goal : Q *)
  iApply "H1". (* goal : P *)
  iExact "H3". (* no more goals *)
Qed.

(*
 * But Iris does not have "iApply ... in". Trying to use it will give you a syntax error.
 *
 * You will implement that today!
 *
 * NOTE: I floated a bit between having you implement a new Iris tactic or learn
 * how to use Iris. I went with the latter because you haven't really had a chance
 * to implement new automation yet, and this is a proof automation class after all.
 * I super recommend checking out the Iris tutorial (also a recommendation from 
 * Robbert Krebbers) if you want to get more of a feel for what using Iris Proof Mode
 * is like: https://gitlab.mpi-sws.org/iris/tutorial-popl21
 *
 * With that in mind, let's implement "iApply ... in", which behaves like "apply ... in"!
 *)
Module Export tac_apply_in.
  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.

  (*
   * We will start with a restricted version of the tactic, then make it more 
   * interesting as go. Remember that tactics in Iris Proof Mode are implemented
   * using a combination of logic programming and computational reflection.
   * So to define a new tactic, we will actually state a Lemma in Coq, then
   * invoke it by ascribing it special syntax in Ltac.
   *
   * Here is our first version if "iApply ... in" (TODO explain, and try the one
   * without IntoWand---simplify as much as possible and then make more interesting.
   * Maybe show them one example before making it incrementally more complicated...
   * also keep simplifying proof---note in eventual version that you make super manual
   * on purpose, but lots of useful automation in the original. actually just leave out part of the proof,
   * have them fill in. offer to help if stuck. tell where to find lemmas, clarify goals.):
   *)
  Lemma tac_apply_in {PROP : bi} (Δ : envs PROP) i j P1 P2 Q:
    envs_lookup i Δ = Some (false, P1 -∗ P2)%I -> (* i maps to P1 -∗ P2 in Δ *)
    envs_lookup j (envs_delete false i false Δ) = Some (false, P1) -> (* j maps to P1 in Δ \ i *)
    (match envs_replace j false false (Esnoc Enil j P2) (envs_delete false i false Δ) with (* IDK *)
    | Some Δ' => envs_entails Δ' Q
    | None => False
    end) ->
    envs_entails Δ Q. (* Q holds in Δ *)
  Proof.
    rewrite envs_entails_eq. intros.
    remember (envs_replace _ _ _ _ _).
    induction o.
    - rewrite (envs_lookup_sound' Δ false i false _ H).
      rewrite (envs_replace_singleton_sound (envs_delete false i false Δ) a j false false _ j _ H0); eauto; simpl in *.
      rewrite assoc.
      rewrite wand_elim_l.
      rewrite wand_elim_r.
      auto.
    - inversion H1.
  Qed.

  (* TODO explain what is happening. add error handling as separate exercise *)
  Tactic Notation "iApply" constr(H1) "in" constr(H2) := 
    refine (tac_apply_in _ H1 H2 _ _ _ _ _ _);
      [pm_reflexivity (* || fail "iApply in:" H1 "not found"*)
      |pm_reflexivity (* || fail "iApply in:" H2 "not found"*)
      |pm_reduce].
End tac_apply_in.


  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.


Lemma test1 {PROP : bi} (P Q R : PROP) : (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "H1 H2 H3".
  (* test errors *)
  (*Fail iApply "H6" in "H3". (* Tactic failure: iApply .. in: "H6" not found. *)
  Fail iApply "H1" in "H5". (* Tactic failure: iApply .. in: "H5" not found. *)
  Fail iApply "H3" in "H1". (* Tactic failure: iApply in: P is not a wand. *)*)

  (* test *)
  iApply "H1" in "H3".
  iApply "H2" in "H3".
  iExact "H3".
Qed.

Lemma test2 {PROP : bi} (P Q R : PROP) : □ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "#H1 H2 H3".
  (* test errors *)
  Fail iApply "H6" in "H3". (* Tactic failure: iApply .. in: "H6" not found. *)
  Fail iApply "H1" in "H5". (* Tactic failure: iApply .. in: "H5" not found. *)
  Fail iApply "H3" in "H1". (* Tactic failure: iApply in: P is not a wand. *)

  (* test *)
  iApply "H1" in "H3".
  iApply "H2" in "H3".
  iExact "H3".
Qed.

(* TODO how to test the wand thing? *)

(* TODO discussion question *)

(* TODO bonus questions *)
