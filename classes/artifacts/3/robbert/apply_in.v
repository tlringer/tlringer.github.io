From iris.proofmode Require Import tactics.

Module Export tac_apply_in.
  Import environments reduction bi.
  Local Open Scope lazy_bool_scope.

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
    - by rewrite HR assoc wand_elim_l wand_elim_r.
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
