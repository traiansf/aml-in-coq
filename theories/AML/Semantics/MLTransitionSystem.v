From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From AML.Lib Require Import Ensemble Traces TransitionSystem.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern Variables Substitution Reachability.
From AML.Semantics Require Import Structure Valuation PatternValuation.

Section sec_transition_system.

Context
  `{ReachabilitySignature}
  (s : Structure)
  .

Definition pattern_valuation_EX_fn : idomain -> Ensemble idomain :=
  pattern_valuation_fn s inhabitant (EX (PEVar inhabitant)) inhabitant.

#[export] Instance ml_transition_system : TransitionSystem idomain :=
  fun a b => a ∈ pattern_valuation_EX_fn b.

Section sec_pattern_valuation_next.

Definition pattern_valuation_EX_functor := image pattern_valuation_EX_fn.

Lemma pattern_valuation_EX_functor_unfold A :
  pattern_valuation_EX_functor A
    ≡
  ext_iapp s (isigma next) A.
Proof.
  unfold pattern_valuation_EX_functor.
  unfold pattern_valuation_EX_fn, image.
  unfold pattern_valuation_fn.
  intro a; rewrite elem_of_filtered_union.
  setoid_rewrite pattern_valuation_app.
  setoid_rewrite elem_of_ext_iapp.
  unfold pattern_valuation.
  setoid_rewrite elem_of_singleton.
  cbn; unfold Functions.fn_update.
  case_decide; [| done].
  by set_solver.
Qed.

Lemma pattern_valuation_EX_fn_unfold a :
  pattern_valuation_EX_fn a
    ≡
  ext_iapp s (isigma next) {[a]}.
Proof.
  rewrite (image_singleton pattern_valuation_EX_fn).
  by apply pattern_valuation_EX_functor_unfold.
Qed.

End sec_pattern_valuation_next.

Section sec_always_finally.

Context
  (e : Valuation)
  (ψ : Pattern)
  .

Definition trace_all_path_finally_pattern : Ensemble idomain :=
  AF_ts (pattern_valuation s e ψ).

Section sec_fix_points.

Context
  (X : SVar)
  (HX_free : X ∉ FSV ψ)
  .

Lemma pattern_valuation_functor_EX ϕ A :
  pattern_valuation_functor s e (EX ϕ) X A
    ≡
  pattern_valuation_EX_functor (pattern_valuation_functor s e ϕ X A).
Proof.
  unfold EX.
  rewrite pattern_valuation_functor_app.
  rewrite pattern_valuation_functor_free at 1 by apply not_elem_of_empty.
  cbn.
  by rewrite pattern_valuation_EX_functor_unfold.
Qed.

Definition phi_or_next_on_all_paths_functor :=
  pattern_valuation_functor s e (ψ ∨ₚ (AX (PSVar X) ∧ₚ can_transition)) X.

Lemma elem_of_phi_or_next_on_all_paths_functor x A :
  x ∈ phi_or_next_on_all_paths_functor A
    <->
  x ∈ pattern_valuation s e ψ
    \/
  ∅ ⊂ transition_image x ⊆ A.
Proof.
  unfold phi_or_next_on_all_paths_functor.
  rewrite pattern_valuation_functor_or,
    pattern_valuation_functor_and.
  unfold AX, can_transition; rewrite pattern_valuation_functor_neg,
    ! pattern_valuation_functor_EX, ! pattern_valuation_EX_functor_unfold,
    pattern_valuation_functor_neg, pattern_valuation_functor_top.
  cbn; rewrite Functions.fn_update_eq.
  rewrite elem_of_union, pattern_valuation_functor_free at 1 by done.
  apply or_iff_compat_l.
  rewrite elem_of_intersection, elem_of_complement, !elem_of_ext_iapp.
  split.
  - intros (Hnex & b & Hb & c & _ & Hx).
    assert
      (Hall : forall b, b ∈ isigma next ->
        forall c, x ∈ iapp b c -> c ∈ A).
    {
      intros b' Hb' c' Hc'.
      apply not_ex_all_not with (n := b') in Hnex.
      apply not_and_or in Hnex.
      pose proof (Hnex' := or_to_imply _ _ Hnex Hb').
      apply not_ex_all_not with (n := c') in Hnex'.
      destruct (classic (c' ∈ A)); [done |].
      contradict Hnex'; split; [| done].
      by apply elem_of_complement.
    }
    repeat split.
    + apply empty_subseteq.
    + intros Hsub.
      cut (exists a, a ∈ transition_image x).
      { by intros [a Ha]; apply Hsub in Ha; contradict Ha; apply not_elem_of_empty. }
      specialize (Hall b Hb c Hx).
      exists c; cbn.
      rewrite Functions.fn_update_eq.
      by unfold ext_iapp; set_solver.
    + intros a; cbn.
      rewrite Functions.fn_update_eq.
      by unfold ext_iapp; set_solver.
  - intros [[_ Hnempty] HsubA].
    split.
    + intros (b & Hb & c & Hnc & Hx).
      rewrite elem_of_complement in Hnc.
      contradict Hnc; apply HsubA; cbn.
      rewrite Functions.fn_update_eq.
      by unfold ext_iapp; set_solver.
    + destruct (classic (exists a, a ∈ transition_image x))
        as [[a Ha] | Hnex].
      * cbn in Ha.
        rewrite Functions.fn_update_eq in Ha.
        by unfold ext_iapp in Ha; set_solver.
      * contradict Hnempty; intros a Ha.
        by contradict Hnex; eexists.
Qed.

Lemma elem_of_phi_or_next_on_all_paths_functor_alt A :
  phi_or_next_on_all_paths_functor A
    ≡
  AF_ts_fixed_point_functor (pattern_valuation s e ψ) A.
Proof.
  intro x; rewrite elem_of_phi_or_next_on_all_paths_functor.
  by rewrite <- reducible_transition_image, transition_image_subseteq.
Qed.

Lemma trace_all_path_finally_pattern_fixpoint :
  fixpoint phi_or_next_on_all_paths_functor trace_all_path_finally_pattern.
Proof.
  eapply fixpoint_equiv;
    [by intro; apply elem_of_phi_or_next_on_all_paths_functor_alt |].
  by apply AF_ts_fixpoint.
Qed.

Lemma trace_all_path_finally_pattern_least_pre_fixpoint A :
  pre_fixpoint phi_or_next_on_all_paths_functor A ->
  trace_all_path_finally_pattern ⊆ A.
Proof.
  intros Hpre.
  apply AF_ts_least_pre_fixpoint.
  eapply pre_fixpoint_equiv; [| done].
  by intro; symmetry; apply elem_of_phi_or_next_on_all_paths_functor_alt.
Qed.

End sec_fix_points.

End sec_always_finally.

End sec_transition_system.
