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
Lemma show_iApply {PROP : bi} (P Q R : PROP) : □ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
Proof.
  iIntros "#H1 H2 H3". (* goal : R *)
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
   * also keep simplifying proof):
   *)
  Lemma tac_apply_in {PROP : bi} (Δ : envs PROP) i j P1 P2 R Q :
    envs_lookup i Δ = Some (false, R) ->
    let Δ' := envs_delete false i false Δ in
    envs_lookup j Δ' = Some (false, P1) ->
    IntoWand false false R P1 P2 ->
    (match envs_replace j false false (Esnoc Enil j P2) Δ' with
    | Some Δ'' => envs_entails Δ'' Q
    | None => False
    end) ->
    envs_entails Δ Q.
  Proof.
    rewrite envs_entails_eq. rewrite /IntoWand. intros.
    remember (envs_replace _ _ _ _ _).
    destruct o.
    - rewrite (envs_lookup_sound' Δ false i false R).
      + rewrite (envs_replace_singleton_sound (envs_delete false i false Δ) e j false false P1 j P2); simpl in *.
        * rewrite H1 assoc wand_elim_l wand_elim_r.
          apply H2.
        * apply H0.
        * symmetry. apply Heqo.
      + apply H.
    - inversion H2.
  Qed.

(*
- Drop support for the intuitionistic context (i.e., use `false` instead
of these Booleans `pi` and `pj` everywhere.)
- Don't attempt error reporting at all.
  - Instead of using the Type class `IntoWand`, have a premise
  `envs_lookup i Δ = Some (pi, P -∗ Q)%I`. This means that the tactic only
works at hypotheses that are syntactically equal to a wand, instead of
those that can be semantically converted into a wand.*)

  Lemma tac_apply_in {PROP : bi} (Δ : envs PROP) i pi j pj P1 P2 R Q :
    envs_lookup i Δ = Some (pi, R) →
    let Δ' := envs_delete false i pi Δ in
    envs_lookup j Δ' = Some (pj, P1) →
    IntoWand pi pj R P1 P2 →
    match envs_replace j pj (pi &&& pj) (Esnoc Enil j P2) Δ' with
    | Some Δ'' => envs_entails Δ'' Q
    | None => False
    end → envs_entails Δ Q.
  Proof.
    rewrite envs_entails_eq /IntoWand. intros ?? HR ?.
    destruct (envs_replace _ _ _ _ _) as [Δ''|] eqn:?; last done.
    rewrite (envs_lookup_sound' _ false) //.
    rewrite envs_replace_singleton_sound //. destruct pi; simpl in *.
    - rewrite -{1}intuitionistically_idemp -{1}intuitionistically_if_idemp.
      rewrite {1}(intuitionistically_intuitionistically_if pj).
      by rewrite HR assoc intuitionistically_if_sep_2 wand_elim_l wand_elim_r.
    - by rewrite HR assoc wand_elim_l wand_elim_r.*)
  Qed.

  Tactic Notation "iApply" constr(H1) "in" constr(H2) :=
    notypeclasses refine (tac_apply_in _ H1 _ H2 _ _ _ _ _ _ _ _ _);
      [pm_reflexivity || fail "iApply in:" H1 "not found"
      |pm_reflexivity || fail "iApply in:" H2 "not found"
      |iSolveTC ||
       let R := match goal with |- IntoWand _ _ ?R _ _ => R end in
       fail "iApply in:" R "is not a wand"
      |pm_reduce].
End tac_apply_in.

Lemma test {PROP : bi} (P Q R : PROP) : □ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R.
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
