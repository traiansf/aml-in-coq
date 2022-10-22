From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Valuation PropositionalPatternValuation PatternValuation Satisfaction.

Section sec_validity.

Context
  [sign : signature]
  .

Definition valid phi : Prop := forall (s : Structure), satisfies s phi.

Lemma valid_top : valid (@pTop sign).
Proof. by intro; apply satisfies_top. Qed.

Lemma valid_and_classic phi psi :
  valid (pAnd phi psi) <-> valid phi /\ valid psi.
Proof.
  unfold valid; setoid_rewrite satisfies_and_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_iff_alt_classic phi psi :
  valid (pIff phi psi) <-> valid (PImpl phi psi) /\ valid (PImpl psi phi).
Proof.
  unfold valid; setoid_rewrite satisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_mp_classic phi psi :
  valid (PImpl phi psi) -> valid phi -> valid psi.
Proof.
  intros Himpl Hphi s.
  eapply satisfies_mp_classic; [apply Himpl | apply Hphi].
Qed.

Lemma valid_iff_classic phi psi :
  valid (pIff phi psi) -> (valid phi <-> valid psi).
Proof.
  rewrite valid_iff_alt_classic; intros [Himpl Himpl'].
  by split; apply valid_mp_classic.
Qed.

Lemma valid_phi_iff_phi phi :  valid (pIff phi phi).
Proof.
  by intros s e; apply top_pattern_valuation_iff_classic; [typeclasses eauto |].
Qed.

Lemma valid_finite_conjunction_classic phis :
  valid (finite_conjunction phis) <-> Forall valid phis.
Proof.
  unfold valid; setoid_rewrite satisfies_finite_conjunction_classic.
  setoid_rewrite Forall_forall.
  itauto.
Qed.

Lemma valid_evar_sub0_rename_ex x y phi :
  EFreeFor x (PEVar y) phi ->
  valid (PImpl (evar_sub0 x (PEVar y) phi) (PEx x phi)).
Proof.
  intros ? ? ?; apply esatisfies_impl_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_union (λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi)).
Qed.

Lemma valid_evar_sub0_rename_all x y phi :
  EFreeFor x (PEVar y) phi ->
  valid (PImpl (pAll x phi) (evar_sub0 x (PEVar y) phi)).
Proof.
  intros ? ? ?; rewrite esatisfies_impl_classic, pattern_valuation_forall_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_intersection (λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi)).
Qed.

Context `{FinSet EVar EVarSet} `{FinSet SVar SVarSet}.

Lemma valid_evar_rename x y phi :
  ~ EOccurs y phi ->
  EFreeFor x (PEVar y) phi ->
  valid (pIff phi (evar_rename x y phi)).
Proof.
  intros Hy Hfree_for.
  destruct (decide (x = y));
    [by subst; rewrite evar_rename_id; apply valid_phi_iff_phi |].
  intros s e.
  apply esatisfies_iff_classic.
  revert e; induction phi; intro. 1-3, 8: done.
  - apply EFreeForImpl in Hfree_for as [].
    rewrite EOccurs_impl in Hy by done; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
  - rewrite EOccurs_ex in Hy by done; apply not_or_and in Hy as [? Hy].
    cbn; case_decide; cbn; intro a; rewrite !elem_of_indexed_union; apply exist_proper; intro b;
      [| by rewrite IHphi; [done..| eapply EFreeForEx]].
    subst e.
    assert (EFreeFor x (PEVar y) (evar_rename x y phi)).
      by (eapply EFreeForInd_iff, evar_rename_FreeFor; [..| rewrite <- EOccursInd_iff]; done).
    rewrite pattern_valuation_evar_sub0_evar by done.
    apply EFreeForEx in Hfree_for as [].
    rewrite <- IHphi, valuation_eupdate_eq by done.
    apply pattern_valuation_fv; destruct e0; split; cbn; [| done].
    intros z Hz; unfold fn_update; case_decide; [done |].
    case_decide; [| done].
    by subst; contradict Hy; left.
  - cbn; intro a; rewrite !elem_of_filtered_intersection; apply forall_proper; intro A.
    rewrite EOccurs_mu in Hy by done.
    by rewrite IHphi; [..| eapply EFreeForMu].
  - apply EFreeForApp in Hfree_for as [].
    rewrite EOccurs_app in Hy by done; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
Qed.

(*
Lemma valid_evar_sub_rename x y phi :
  valid (PImpl (esubst phi x (PEVar y)) (PEx x phi)).
Proof.
  unfold esubst, SV, EV; cbn.
  replace (elements (BSV phi ∩ _)) with (@nil SVar)
    by (symmetry; apply elements_empty_iff; set_solver).
  cbn; destruct (decide (EVarBound y phi)); cycle 1.
  - replace (elements _) with (@nil EVar).
    + cbn; apply valid_evar_sub0_rename_ex.
      by apply EFreeFor_x_y_if_not_bound.
    + symmetry; apply elements_empty_iff, elem_of_equiv_empty; intro.
      rewrite elem_of_intersection, elem_of_union, elem_of_singleton, <- EVarBound_BEV.
      by intros [? [|Hempty]]; [subst | contradict Hempty; apply not_elem_of_empty].
  - replace (elements _) with [y]; cycle 1.
    {
      apply Permutation_singleton_l.
      rewrite <- elements_singleton.
      apply elements_proper.
      intro a; rewrite elem_of_intersection, elem_of_union, !elem_of_singleton.
      rewrite <- EVarBound_BEV.
      split; [by intros ->; split; [| left] | intros [? [-> | Hempty]]]; [done |].
      contradict Hempty; apply not_elem_of_empty.
    }
    cbn.
*)

End sec_validity.
