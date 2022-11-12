From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Valuation PropositionalPatternValuation PatternValuation Satisfaction.

Section sec_validity.

Context `{signature}.

Definition valid phi : Prop := forall (s : Structure), satisfies s phi.

Definition valid_impl : relation Pattern := fun phi psi => valid (PImpl phi psi).

#[export] Instance valid_impl_refl : Reflexive valid_impl.
Proof. by intros phi s e; apply esatisfies_impl_classic. Qed.

#[export] Instance valid_impl_tran : Transitive valid_impl.
Proof.
  intros phi psi chi Hphi Hpsi s e; apply esatisfies_impl_classic.
  transitivity (pattern_valuation s e psi); apply esatisfies_impl_classic.
  - by apply Hphi.
  - by apply Hpsi.
Qed.

Definition valid_iff : relation Pattern := fun phi psi => valid (pIff phi psi).

Local Notation "A `valid_impl` B" := (valid_impl A B) (at level 90).
Local Notation "A `valid_iff` B" := (valid_iff A B) (at level 90).

#[export] Instance valid_iff_refl : Reflexive valid_iff.
Proof. by intros phi s e; apply esatisfies_iff_classic. Qed.

#[export] Instance valid_iff_tran : Transitive valid_iff.
Proof.
  intros phi psi chi Hphi Hpsi s e; apply esatisfies_iff_classic.
  transitivity (pattern_valuation s e psi); apply esatisfies_iff_classic.
  - by apply Hphi.
  - by apply Hpsi.
Qed.

#[export] Instance valid_iff_sym : Symmetric valid_iff.
Proof.
  intros phi psi Hphi s e; apply esatisfies_iff_classic.
  symmetry; apply esatisfies_iff_classic, Hphi.
Qed.

Lemma valid_top : valid pTop.
Proof. by intro; apply satisfies_top. Qed.

Lemma valid_and_classic phi psi :
  valid (pAnd phi psi) <-> valid phi /\ valid psi.
Proof.
  unfold valid; setoid_rewrite satisfies_and_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_iff_alt_classic phi psi :
  (phi `valid_iff` psi) <-> (phi `valid_impl` psi) /\ (psi `valid_impl` phi).
Proof.
  unfold valid_iff, valid; setoid_rewrite satisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma valid_mp_classic phi psi :
  phi `valid_impl` psi -> valid phi -> valid psi.
Proof.
  intros Himpl Hphi s.
  eapply satisfies_mp_classic; [apply Himpl | apply Hphi].
Qed.

Lemma valid_iff_classic phi psi :
  phi `valid_iff` psi -> (valid phi <-> valid psi).
Proof.
  rewrite valid_iff_alt_classic; intros [Himpl Himpl'].
  by split; apply valid_mp_classic.
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
  evar_sub0 x (PEVar y) phi `valid_impl` PEx x phi.
Proof.
  intros ? ? ?; apply esatisfies_impl_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_union (λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi)).
Qed.

Lemma valid_evar_sub0_rename_all x y phi :
  EFreeFor x (PEVar y) phi ->
  pAll x phi `valid_impl` evar_sub0 x (PEVar y) phi.
Proof.
  intros ? ? ?; rewrite esatisfies_impl_classic, pattern_valuation_forall_classic.
  rewrite pattern_valuation_evar_sub0_evar by done; cbn.
  apply (member_of_indexed_intersection (λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi)).
Qed.

Lemma valid_evar_rename x y phi :
  ~ EOccurs y phi ->
  phi `valid_iff` evar_rename x y phi.
Proof.
  intros Hy.
  assert (Hfree_for : EFreeFor x (PEVar y) phi).
  {
    apply EFreeFor_x_y_if_not_bound; contradict Hy; right; done.
  }
  destruct (decide (x = y));
    [by subst; rewrite evar_rename_id |].
  intros s e.
  apply esatisfies_iff_classic.
  revert e; induction phi; intro. 1-2, 7: done.
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

Lemma valid_esubst_ex x y phi :
  esubst phi x (PEVar y) `valid_impl` PEx x phi.
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
    remember (fresh _) as z.
    assert (~ EOccurs z phi /\ z <> y) as [Hnoccurs Hnyz].
    {
      pose proof (Hz := is_fresh (FEV phi ∪ BEV phi ∪ ({[y]} ∪ ∅))).
      rewrite <- Heqz, !elem_of_union, elem_of_singleton in Hz.
      rewrite EV_Eoccurs; unfold EV; rewrite elem_of_union.
      by intuition.
    }
    remember (evar_rename _ _ _) as theta.
    assert (Hxfree : EFreeFor x (PEVar y) theta).
    {
      by subst theta; apply EFreeForInd_iff, evar_rename_FreeFor_1; [| rewrite <- EOccursInd_iff].
    }
    assert (Htheta_ex : valid (PImpl (evar_sub0 x (PEVar y) theta) (PEx x theta)))
      by (apply valid_evar_sub0_rename_ex; done).
    assert (Htheta_phi : valid (pIff theta phi)).
    {
      symmetry; subst theta; apply valid_evar_rename; done.
    }
    intros s v; apply esatisfies_impl_classic; cbn.
    specialize (Htheta_ex s v); apply esatisfies_impl_classic in Htheta_ex; cbn in Htheta_ex.
    etransitivity; [apply Htheta_ex |].
    intro a; rewrite !elem_of_indexed_union.
    apply exist_proper; intro b.
    specialize (Htheta_phi s (valuation_eupdate v x b)); apply esatisfies_iff_classic in Htheta_phi.
    by symmetry; apply Htheta_phi.
Qed.
    
Lemma valid_esubst_all x y phi :
  pAll x phi `valid_impl` esubst phi x (PEVar y).
Proof.
  unfold esubst, SV, EV; cbn.
  replace (elements (BSV phi ∩ _)) with (@nil SVar)
    by (symmetry; apply elements_empty_iff; set_solver).
  cbn; destruct (decide (EVarBound y phi)); cycle 1.
  - replace (elements _) with (@nil EVar).
    + cbn; apply valid_evar_sub0_rename_all.
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
    remember (fresh _) as z.
    assert (~ EOccurs z phi /\ z <> y) as [Hnoccurs Hnyz].
    {
      pose proof (Hz := is_fresh (FEV phi ∪ BEV phi ∪ ({[y]} ∪ ∅))).
      rewrite <- Heqz, !elem_of_union, elem_of_singleton in Hz.
      rewrite EV_Eoccurs; unfold EV; rewrite elem_of_union.
      by intuition.
    }
    remember (evar_rename _ _ _) as theta.
    assert (Hxfree : EFreeFor x (PEVar y) theta).
    {
      by subst theta; apply EFreeForInd_iff, evar_rename_FreeFor_1; [| rewrite <- EOccursInd_iff].
    }
    assert (Htheta_all : valid (PImpl (pAll x theta) (evar_sub0 x (PEVar y) theta)))
      by (apply valid_evar_sub0_rename_all; done).
    assert (Htheta_phi : valid (pIff theta phi)).
    {
      symmetry; subst theta; apply valid_evar_rename; done.
    }
    intros s v; apply esatisfies_impl_classic; rewrite pattern_valuation_forall_classic.
    specialize (Htheta_all s v); apply esatisfies_impl_classic in Htheta_all.
    rewrite pattern_valuation_forall_classic in Htheta_all.
    etransitivity; [| apply Htheta_all].
    intro a; rewrite !elem_of_indexed_intersection.
    apply forall_proper; intro b.
    specialize (Htheta_phi s (valuation_eupdate v x b)); apply esatisfies_iff_classic in Htheta_phi.
    by apply Htheta_phi.
Qed.
 
Lemma valid_svar_rename x y phi :
  ~ SOccurs y phi ->
  phi `valid_iff` svar_rename x y phi.
Proof.
  intros Hy.
  destruct (decide (x = y));
    [by subst; rewrite svar_rename_id |].
  intros s e.
  apply esatisfies_iff_classic.
  revert e; induction phi; intro. 1-2, 7: done.
  - rewrite SOccurs_impl in Hy by done; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
  - rewrite SOccurs_ex in Hy.
    by cbn; intro a; rewrite !elem_of_indexed_union; apply exist_proper; intro b;
      rewrite IHphi.
  - rewrite SOccurs_mu in Hy by done; apply not_or_and in Hy as [Hys0 Hy].
    cbn; intro a.
    case_decide; cycle 1; cbn; rewrite !elem_of_filtered_intersection;
      apply forall_proper; intro A; [by rewrite <- IHphi | subst s0].
    assert (SFreeFor x (PSVar y) (svar_rename x y phi))
      by (eapply SFreeForInd_iff, svar_rename_FreeFor; [..| rewrite <- SOccursInd_iff]; done).
    rewrite pattern_valuation_svar_sub0_svar by done.
    rewrite <- IHphi, valuation_supdate_eq by done.
    cut (pattern_valuation s (valuation_supdate e x A) phi
      ≡
      pattern_valuation s (valuation_supdate (valuation_supdate e y A) x A) phi);
      [by intros -> |].
    rewrite valuation_supdate_comm by done.
    remember (valuation_supdate e x A) as exA.
    symmetry; apply pattern_valuation_supdate_not_free.
    by contradict Hy; left.
  - rewrite SOccurs_app in Hy by done; apply not_or_and in Hy as [].
    by cbn; rewrite IHphi1, IHphi2.
Qed.

Lemma valid_svar_rename_iter_fresh rename_vars avoid_vars phi :
  rename_vars ⊆ BSV phi -> SV phi ⊆ avoid_vars ->
  let refreshed_phi := 
        svar_rename_iter
          (elements rename_vars)
          (fresh_list (length (elements rename_vars)) avoid_vars)
          phi
  in (refreshed_phi `valid_iff` phi).
Proof.
  remember (elements rename_vars) as l_rename_vars.
  intros H_incl.
  assert (Hincl : Forall (fun x => x ∈ BSV phi) l_rename_vars).
  {
    apply Forall_forall; intros; apply H_incl, elem_of_elements; subst; done.
  }
  clear H_incl rename_vars Heql_rename_vars.
  revert phi Hincl avoid_vars.
  induction l_rename_vars; intros phi Hincl avoid_vars Havoid; cbn; [done |].
  apply Forall_cons in Hincl as [Ha Hincl].
  assert (Havoid' : SV phi ⊆ {[fresh avoid_vars]} ∪ avoid_vars)
    by (apply union_subseteq_r'; done).
  specialize (IHl_rename_vars _ Hincl _ Havoid').
  symmetry; etransitivity; [by symmetry; apply IHl_rename_vars|].
  apply valid_svar_rename, svar_rename_iter_fresh_not_occurs.
  - rewrite SV_Soccurs.
    intros Hfresh; apply Havoid in Hfresh.
    contradict Hfresh; apply is_fresh; done.
  - intros Hfresh; apply fresh_list_is_fresh in Hfresh.
    contradict Hfresh; rewrite elem_of_union, elem_of_singleton; left; done.
Qed.

Lemma valid_evar_rename_iter_fresh rename_vars avoid_vars phi :
  rename_vars ⊆ BEV phi -> EV phi ⊆ avoid_vars ->
  let refreshed_phi := 
        evar_rename_iter
          (elements rename_vars)
          (fresh_list (length (elements rename_vars)) avoid_vars)
          phi
  in (refreshed_phi `valid_iff` phi).
Proof.
  remember (elements rename_vars) as l_rename_vars.
  intros H_incl.
  assert (Hincl : Forall (fun x => x ∈ BEV phi) l_rename_vars).
  {
    apply Forall_forall; intros; apply H_incl, elem_of_elements; subst; done.
  }
  clear H_incl rename_vars Heql_rename_vars.
  revert phi Hincl avoid_vars.
  induction l_rename_vars; intros phi Hincl avoid_vars Havoid; cbn; [done |].
  apply Forall_cons in Hincl as [Ha Hincl].
  assert (Havoid' : EV phi ⊆ {[fresh avoid_vars]} ∪ avoid_vars)
    by (apply union_subseteq_r'; done).
  specialize (IHl_rename_vars _ Hincl _ Havoid').
  symmetry; etransitivity; [by symmetry; apply IHl_rename_vars|].
  apply valid_evar_rename, evar_rename_iter_fresh_not_occurs.
  - rewrite EV_Eoccurs.
    intros Hfresh; apply Havoid in Hfresh.
    contradict Hfresh; apply is_fresh; done.
  - intros Hfresh; apply fresh_list_is_fresh in Hfresh.
    contradict Hfresh; rewrite elem_of_union, elem_of_singleton; left; done.
Qed.

End sec_validity.

Notation "A `valid_impl` B" := (valid_impl A B) (at level 90).
Notation "A `valid_iff` B" := (valid_iff A B) (at level 90).

Section sec_valid_examples.

Context `{signature}.

Lemma valid_all_impl_free x phi : pAll x phi `valid_impl` phi.
Proof.
  intros s e.
  rewrite esatisfies_impl_classic, pattern_valuation_forall_classic; cbn.
  transitivity (pattern_valuation s (valuation_eupdate e x (eval e x)) phi);
    [| by rewrite valuation_eupdate_id].
  by apply (member_of_indexed_intersection ((λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi))).
Qed.

Lemma valid_free_impl_ex x phi : phi `valid_impl` PEx x phi.
Proof.
  intros s e.
  rewrite esatisfies_impl_classic; cbn.
  transitivity (pattern_valuation s (valuation_eupdate e x (eval e x)) phi);
    [by rewrite valuation_eupdate_id |].
  by apply (member_of_indexed_union ((λ a : idomain, pattern_valuation s (valuation_eupdate e x a) phi))).
Qed.

Lemma valid_all_impl_ex x phi : pAll x phi `valid_impl` PEx x phi.
Proof.
  eapply valid_impl_tran; [apply valid_all_impl_free | apply valid_free_impl_ex].
Qed.

Lemma valid_ex_x x : valid (PEx x (PEVar x)).
Proof.
  intros s e.
  apply esatisfies_ex; cbn.
  apply elem_of_equiv_top; intro x'; apply elem_of_indexed_union.
  by exists x'; rewrite fn_update_eq.
Qed.

Lemma valid_all_iff_valid_free x phi :
  valid (pAll x phi) <-> valid phi.
Proof.
  by unfold valid; setoid_rewrite satisfies_all_classic.
Qed.

Lemma valid_remove_unbound_ex x phi :
  ~ EVarFree x phi -> PEx x phi `valid_iff` phi.
Proof.
  intros Hnfree s e.
  apply esatisfies_iff_classic; cbn.
  intro a; rewrite elem_of_indexed_union.
  split; [| by exists (eval e x); rewrite valuation_eupdate_id].
  intros [ax Hax].
  eapply (pattern_valuation_fv); [| done].
  split; [cbn | done].
  intros x' Hx'.
  by unfold fn_update; case_decide; [subst |].
Qed.

Lemma valid_remove_unbound_all x phi :
  ~ EVarFree x phi -> pAll x phi `valid_iff` phi.
Proof.
  intros Hnfree s e.
  rewrite esatisfies_iff_classic, pattern_valuation_forall_classic; cbn.
  intro a; rewrite elem_of_indexed_intersection.
  cut (forall i, pattern_valuation s (valuation_eupdate e x i) phi ≡ pattern_valuation s e phi).
  {
    intros Hall; split.
    - by intro Hall'; apply (Hall inhabitant), Hall'.
    - by intros Ha i; apply Hall.
  }
  intro; apply pattern_valuation_fv.
  split; [cbn | done].
  intros x' Hx'.
  by unfold fn_update; case_decide; [subst |].
Qed.

End sec_valid_examples.

Section sec_application.

Context
  `{signature}.

Lemma valid_iff_app_bot_r phi :  PApp phi pBot `valid_iff` pBot.
Proof.
  intros A e; apply esatisfies_iff_classic.
  rewrite pattern_valuation_app, !pattern_valuation_bot.
  by apply ext_iapp_empty_r.
Qed.

Lemma valid_iff_app_bot_l phi :  PApp pBot phi`valid_iff` pBot.
Proof.
  intros A e; apply esatisfies_iff_classic.
  rewrite pattern_valuation_app, !pattern_valuation_bot.
  by apply ext_iapp_empty_l.
Qed.

Lemma valid_iff_app_or_l phi psi chi :
  PApp (pOr phi psi) chi `valid_iff` pOr (PApp phi chi) (PApp psi chi).
Proof.
  intros A e; apply esatisfies_iff_classic.
  rewrite pattern_valuation_app, !pattern_valuation_or_classic, pattern_valuation_app
    by typeclasses eauto.
  by apply ext_iapp_union_l.
Qed.

Lemma valid_iff_app_or_r phi psi chi :
  PApp chi (pOr phi psi) `valid_iff` pOr (PApp chi phi) (PApp chi psi).
Proof.
  intros A e; apply esatisfies_iff_classic.
  rewrite pattern_valuation_app, !pattern_valuation_or_classic, pattern_valuation_app
    by typeclasses eauto.
  by apply ext_iapp_union_r.
Qed.

Lemma valid_iff_app_ex_l x phi psi :
  ~ x ∈ FEV psi ->
  PApp (PEx x phi) psi `valid_iff` PEx x (PApp phi psi).
Proof.
  intros Hx A e; apply esatisfies_iff_classic.
  cbn; rewrite ext_iapp_indexed_union_l.
  intro a; rewrite !elem_of_indexed_union.
  apply exist_proper; intro b; revert a; apply ext_iapp_Proper; [done |].
  apply pattern_valuation_fv.
  split; [| done].
  intro x'; rewrite EVarFree_FEV; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

Lemma valid_iff_app_ex_r x phi psi :
  ~ x ∈ FEV psi ->
  PApp psi (PEx x phi) `valid_iff` PEx x (PApp psi phi).
Proof.
  intros Hx A e; apply esatisfies_iff_classic.
  cbn; rewrite ext_iapp_indexed_union_r.
  intro a; rewrite !elem_of_indexed_union.
  apply exist_proper; intro b; revert a; apply ext_iapp_Proper; [| done].
  apply pattern_valuation_fv.
  split; [| done].
  intro x'; rewrite EVarFree_FEV; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

Lemma valid_impl_app_and_l phi psi chi :
  PApp (pAnd phi psi) chi `valid_impl` pAnd (PApp phi chi) (PApp psi chi).
Proof.
  intros A e; apply esatisfies_impl_classic.
  rewrite pattern_valuation_app, !pattern_valuation_and_classic, !pattern_valuation_app
    by typeclasses eauto.
  by apply ext_iapp_intersection_l.
Qed.

Lemma valid_impl_app_and_r phi psi chi :
  PApp chi (pAnd phi psi) `valid_impl` pAnd (PApp chi phi) (PApp chi psi).
Proof.
  intros A e; apply esatisfies_impl_classic.
  rewrite pattern_valuation_app, !pattern_valuation_and_classic, !pattern_valuation_app
    by typeclasses eauto.
  by apply ext_iapp_intersection_r.
Qed.

Lemma valid_impl_app_all_l x phi psi :
  ~ x ∈ FEV psi ->
  PApp (pAll x phi) psi `valid_impl` pAll x (PApp phi psi).
Proof.
  intros Hx A e; apply esatisfies_impl_classic.
  rewrite pattern_valuation_app, !pattern_valuation_forall_classic. 
  cbn; rewrite ext_iapp_indexed_intersection_l.
  intro a; rewrite !elem_of_indexed_intersection.
  apply forall_proper; intro b; revert a; apply ext_iapp_Proper; [done |].
  apply pattern_valuation_fv.
  split; [| done].
  intro x'; rewrite EVarFree_FEV; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

Lemma valid_impl_app_all_r x phi psi :
  ~ x ∈ FEV psi ->
  PApp psi (pAll x phi) `valid_impl` pAll x (PApp psi phi).
Proof.
  intros Hx A e; apply esatisfies_impl_classic.
  rewrite pattern_valuation_app, !pattern_valuation_forall_classic. 
  cbn; rewrite ext_iapp_indexed_intersection_r.
  intro a; rewrite !elem_of_indexed_intersection.
  apply forall_proper; intro b; revert a; apply ext_iapp_Proper; [| done].
  apply pattern_valuation_fv.
  split; [| done].
  intro x'; rewrite EVarFree_FEV; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

End sec_application.

Section sec_mu.

End sec_mu.
