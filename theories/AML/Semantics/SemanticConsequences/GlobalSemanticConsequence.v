From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.
From sets Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Tautology.
From AML Require Import StrongSemanticConsequence LocalSemanticConsequence.

Definition global_semantic_consequence `{signature} (ϕ ψ : Pattern) : Prop :=
  forall (s : Structure), satisfies s ϕ -> satisfies s ψ.

Definition globally_logically_equivalent `{signature} (ϕ ψ : Pattern) : Prop :=
  forall (s : Structure), satisfies s ϕ <-> satisfies s ψ.

Notation "{ phi } ⊧ psi" := (global_semantic_consequence phi psi) (at level 60, no associativity) : ml_scope.

#[export] Instance globally_logically_equivalent_equiv `{signature} :
  Equiv Pattern := globally_logically_equivalent.

Section sec_global_semantic_consequence.

Context `{signature}.

#[export] Instance global_semantic_consequence_refl : Reflexive global_semantic_consequence.
Proof. by intros ? ?. Qed.

#[export] Instance global_semantic_consequence_trans : Transitive global_semantic_consequence.
Proof.
  intros ϕ ψ χ Hψ Hchi s Hϕ.
  by apply Hchi, Hψ.
Qed.

#[export] Instance globally_logically_equivalent_refl : Reflexive globally_logically_equivalent.
Proof. by intros ? ?. Qed.

#[export] Instance globally_logically_equivalent_trans : Transitive globally_logically_equivalent.
Proof.
  intros ϕ ψ χ Hψ Hchi s.
  by etransitivity; [apply Hψ | apply Hchi].
Qed.

#[export] Instance globally_logically_equivalent_sym : Symmetric globally_logically_equivalent.
Proof.
  intros ϕ ψ Hψ s.
  by symmetry.
Qed.

Lemma globally_logically_equivalent_iff ϕ ψ :
  ϕ ≡ ψ
    <->
  {ϕ} ⊧ ψ /\ {ψ} ⊧ ϕ.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance global_semantic_consequence_satisfies s :
  Proper (global_semantic_consequence ==> Basics.impl) (satisfies s).
Proof. by intros ϕ ψ Hcns Hϕ; apply Hcns, Hϕ. Qed.

#[export] Instance global_semantic_consequence_valid :
  Proper (global_semantic_consequence ==> Basics.impl) valid.
Proof. intros ϕ ψ Hcns Hϕ s; rewrite <- Hcns; apply Hϕ. Qed.

#[export] Instance globally_logically_equivalent_satisfies s :
  Proper ((≡) ==> iff) (satisfies s).
Proof.
  intros ϕ ψ; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance globally_logically_equivalent_valid :
  Proper ((≡) ==> iff) valid.
Proof. by intros ϕ ψ Heqv; unfold valid, Validity.valid; setoid_rewrite Heqv. Qed.

Lemma local_semantic_consequence_global ϕ ψ :
  {ϕ} ⊧ₗ ψ -> {ϕ} ⊧ ψ.
Proof. by intros Hlocal s Hϕ e; apply Hlocal, Hϕ. Qed.

Lemma locally_logically_equivalent_global ϕ ψ :
  ϕ ≡ₗ ψ -> ϕ ≡ ψ.
Proof.
  rewrite locally_logically_equivalent_iff, globally_logically_equivalent_iff.
  by intros []; split; apply local_semantic_consequence_global.
Qed.

Lemma globally_logically_equivalent_evar x y :
  PEVar x ≡ PEVar y.
Proof.
  by apply locally_logically_equivalent_global, locally_logically_equivalent_evar.
Qed.

Lemma globally_logically_equivalent_not_local :
  exists ϕ ψ, ϕ ≡ ψ /\ ~ {ϕ} ⊧ₗ ψ.
Proof.
  assert (exists x y : EVar, x <> y) as (x & y & Hxy).
  {
    pose (x := fresh [] : EVar ).
    exists x, (fresh [x]).
    intro Hx.
    by apply infinite_is_fresh with [x], elem_of_list_singleton.
  }
  exists (pOr (PEVar x) (PEVar y)), (pAnd (PEVar x) (PEVar y)); split.
  - intro s; cbn. rewrite satisfies_and_classic; split; cycle 1; unfold satisfies, esatisfies.
    + intros [Hx Hy] e.
      rewrite top_pattern_valuation_or_classic by typeclasses eauto.
      unfold satisfies, esatisfies in Hx. rewrite (Hx e).
      set_solver.
    + intro Hor.
      specialize (Hor (valuation_eupdate inhabitant y (eval inhabitant x))).
      rewrite top_pattern_valuation_or_classic in Hor by typeclasses eauto.
      rewrite subseteq_union_1 in Hor
        by (cbn; unfold fn_update; rewrite decide_False, decide_True; done).
      cbn in Hor; unfold fn_update in Hor; rewrite decide_True in Hor by done.
      by split; apply satisfies_evar; eexists.
  - intro Hlocal.
    pose (s := {| idomain := bool; non_empty := populate true;
                  iapp := fun x y z => False; isigma := fun x y => False |}).
    specialize (Hlocal s (valuation_eupdate (valuation_eupdate inhabitant x true) y false)).
    unfold esatisfies in Hlocal.
    rewrite top_pattern_valuation_and_classic in Hlocal by typeclasses eauto.
    feed specialize Hlocal.
    {
      rewrite top_pattern_valuation_or_classic by typeclasses eauto.
      cbn; rewrite fn_update_eq.
      unfold fn_update at 1; rewrite decide_False by done.
      rewrite fn_update_eq.
      intros []; set_solver.
    }
    destruct Hlocal as [Hx Hy].
    apply esatisfies_evar in Hx as [a Ha].
    cbn in Ha.
    cut (true = false); [done |].
    by transitivity a; [| symmetry];
      eapply elem_of_singleton; rewrite <- Ha.
    Unshelve. all: typeclasses eauto.
Qed.

Lemma global_semantic_consequence_not_local :
  exists ϕ ψ, {ϕ} ⊧ ψ /\ ~ {ϕ} ⊧ₗ ψ.
Proof.
  destruct globally_logically_equivalent_not_local as (ϕ & ψ & Heqv & Hncons).
  by exists ϕ, ψ; split; [apply globally_logically_equivalent_iff in Heqv as [] |].
Qed.

Lemma globally_logically_equivalent_not_locally :
  exists ϕ ψ, ϕ ≡ ψ /\ ~ ϕ ≡ₗ ψ.
Proof.
  destruct globally_logically_equivalent_not_local as (ϕ & ψ & Heqv & Hncons).
  exists ϕ, ψ; split; [done |].
  by contradict Hncons; apply locally_logically_equivalent_iff in Hncons as [].
Qed.

End sec_global_semantic_consequence.

Section sec_set_global_semantic_consequence_definition.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Definition set_global_semantic_consequence (Gamma : PatternSet) (ϕ : Pattern) :=
  forall s, set_satisfies s Gamma -> satisfies s ϕ.

#[export] Instance set_global_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _ϕ ϕ ->.
  by unfold set_global_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_global_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _ϕ ϕ -> HGamma' s HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_global_semantic_consequence_singleton ϕ ψ :
  set_global_semantic_consequence {[ϕ]} ψ <-> {ϕ} ⊧ ψ.
Proof.
  unfold set_global_semantic_consequence, global_semantic_consequence.
  by setoid_rewrite set_satisfies_singleton.
Qed.

Lemma set_global_semantic_consequence_empty_valid ϕ :
  set_global_semantic_consequence ∅ ϕ <-> valid ϕ.
Proof.
  unfold set_global_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intro Hempty; apply Hempty; intros e _ϕ H_ϕ.
  contradict H_ϕ; apply not_elem_of_empty.
Qed.

End sec_set_global_semantic_consequence_definition.

Infix "⊧" := set_global_semantic_consequence (at level 60, no associativity) : ml_scope.

Section sec_set_global_semantic_consequence.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Lemma set_global_semantic_consequence_union_left (Gamma Gamma' : PatternSet) ϕ :
  Gamma ⊧ ϕ ->
  Gamma ∪ Gamma' ⊧ ϕ.
Proof.
  intros HGamma.
  eapply set_global_semantic_consequence_proper_subseteq; [| done..].
  by eapply union_subseteq_l.
Qed.

Lemma set_global_semantic_consequence_union_right (Gamma Gamma' : PatternSet) ϕ :
  Gamma' ⊧ ϕ ->
  Gamma ∪ Gamma' ⊧ ϕ.
Proof.
  intros HGamma.
  eapply set_global_semantic_consequence_proper_subseteq; [| done..].
  by eapply union_subseteq_r.
Qed.

Lemma set_local_semantic_consequence_global (Gamma : PatternSet) ϕ :
  Gamma ⊧ₗ ϕ -> Gamma ⊧ ϕ.
Proof. by intros Hlocal s Hϕ e; apply Hlocal, Hϕ. Qed.

Lemma valid_set_global_semantic_consequence_any ϕ (Gamma : PatternSet) :
  valid ϕ -> Gamma ⊧ ϕ.
Proof.
  by intro; apply set_local_semantic_consequence_global,
    valid_set_local_semantic_consequence_any.
Qed.

#[export] Instance global_semantic_consequence_set_consequence (Gamma : PatternSet) :
  Proper (global_semantic_consequence ==> Basics.impl) (set_global_semantic_consequence Gamma).
Proof. by intros ϕ ψ Hcns Hϕ s HGamma; apply Hcns, Hϕ. Qed.

#[export] Instance globally_logically_equivalent_set_consequence (Gamma : PatternSet) :
  Proper ((≡) ==> iff) (set_global_semantic_consequence Gamma).
Proof.
  intros ϕ ψ; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_global_semantic_consequence_and (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ ϕ ∧ₚ ψ
    <->
  Gamma ⊧ ϕ /\ Gamma ⊧ ψ.
Proof.
  unfold set_global_semantic_consequence.
  setoid_rewrite satisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_global_semantic_consequence_iff (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ ϕ ↔ₚ ψ
    <->
  Gamma ⊧ ϕ →ₚ ψ
    /\
  Gamma ⊧ ψ →ₚ ϕ.
Proof.
  unfold set_global_semantic_consequence; setoid_rewrite satisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_global_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure), set_satisfies s Gamma -> set_satisfies s Delta.

Infix "|=" := set_global_semantic_consequence_set (at level 60, no associativity) : ml_scope.

#[export] Instance set_global_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_global_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_global_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_global_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_global_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_global_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_global_semantic_consequence_set_satisfies_proper s :
  Proper (set_global_semantic_consequence_set ==> Basics.impl) (set_satisfies s).
Proof. by intros Gamma Delta HGammaDelta HGamma; apply HGammaDelta. Qed.

Definition set_globally_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure), set_satisfies s Gamma <-> set_satisfies s Delta.

#[export] Instance set_globally_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_globally_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_globally_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_globally_logically_equivalent_set_proper_iff Gamma Delta :
  set_globally_logically_equivalent_set Gamma Delta
    <->
  Gamma |= Delta /\ Delta |= Gamma .
Proof.
  unfold set_globally_logically_equivalent_set, set_global_semantic_consequence_set.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_globally_logically_equivalent_set_set_satisfies_proper s :
  Proper (set_globally_logically_equivalent_set ==> iff) (set_satisfies s).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_globally_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_global_semantic_consequence_set_consequence_proper :
  Proper (set_global_semantic_consequence_set --> globally_logically_equivalent ==> Basics.impl)
    set_global_semantic_consequence.
Proof.
  intros Delta Gamma HDelta ϕ ψ Hϕψ Hϕ s HGamma.
  by rewrite <- Hϕψ; apply Hϕ; rewrite HDelta.
Qed.

#[export] Instance set_globally_logically_equivalent_set_consequence_proper :
  Proper (set_globally_logically_equivalent_set ==> globally_logically_equivalent ==> iff)
    set_global_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv ϕ ψ Heqv; unfold set_global_semantic_consequence.
  by setoid_rewrite Hset_eqv; setoid_rewrite Heqv.
Qed.

Lemma set_globally_logically_equivalent_set_finite_classic
  `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_globally_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intro s.
  rewrite set_satisfies_singleton, satisfies_finite_conjunction_classic, Forall_forall by done.
  unfold set_satisfies, set_esatisfies, satisfies.
  setoid_rewrite elem_of_elements.
  itauto.
Qed.

Lemma set_local_semantic_consequence_global_closed_pattern (Gamma : PatternSet) ϕ :
  set_closed_pattern Gamma ->
    Gamma ⊧ₗ ϕ
      <->
    Gamma ⊧ ϕ.
Proof.
  split; [by apply set_local_semantic_consequence_global |].
  intros Hglobal s e HGamma; apply Hglobal.
  by eapply set_satistifes_closed_pattern; [| eexists].
Qed.

Section sec_rules.

Lemma set_global_mp (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ ϕ ->
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ ψ.
Proof.
  intros Hϕ Hϕψ A HGamma e.
  specialize (Hϕ A HGamma e).
  specialize (Hϕψ A HGamma e).
  by eapply esatisfies_mp_classic.
Qed.

Lemma set_global_impl_trans (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ ψ →ₚ χ ->
  Gamma ⊧ ψ →ₚ χ.
Proof.
  intros Hϕψ Hψchi A HGamma e.
  specialize (Hϕψ A HGamma e).
  specialize (Hψchi A HGamma e).
  rewrite esatisfies_impl_classic in Hϕψ, Hψchi |- *.
  by etransitivity.
Qed.

Lemma set_global_and_curry (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ ∧ₚ ψ →ₚ χ
    <->
  Gamma ⊧ ϕ →ₚ ψ →ₚ χ.
Proof.
  pose proof (Hcurry := tautology_impl_impl_and ϕ ψ χ).
  apply tautology_valid, strongly_logically_equivalent_valid,
    strongly_logically_equivalent_locally, locally_logically_equivalent_global in Hcurry.
  by rewrite Hcurry.
Qed.

Lemma set_global_impl_ex_elim (Gamma : PatternSet) ϕ ψ x :
  Gamma ⊧ ϕ →ₚ ψ ->
  x ∉ FEV ψ ->
  Gamma ⊧ PEx x ϕ →ₚ ψ.
Proof.
  intros Hϕψ Hx A HGamma e.
  specialize (Hϕψ A HGamma).
  apply esatisfies_impl_classic; cbn.
  unfold satisfies in Hϕψ; setoid_rewrite esatisfies_impl_classic in Hϕψ.
  intro a; rewrite elem_of_indexed_union.
  intros [xa Hxa].
  apply Hϕψ in Hxa.
  cut (pattern_valuation A (valuation_eupdate e x xa) ψ ≡ pattern_valuation A e ψ);
    [by set_solver |].
  apply pattern_valuation_fv.
  split; [| done].
  rewrite <- EVarFree_FEV in Hx.
  intros x' Hx'; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

End sec_rules.

Section sec_application.

Lemma global_semantic_consequence_impl_app_r ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_impl_app_l ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_iff_app_r ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ PApp χ ϕ ↔ₚ PApp χ ψ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_iff_app_l ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ PApp ϕ χ ↔ₚ PApp ψ χ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; cbn.
  by intros Hincl e; eapply ext_iapp_Proper.
Qed.

Lemma global_semantic_consequence_impl_neg ϕ ψ :
  {ϕ →ₚ ψ} ⊧ ¬ₚ ψ →ₚ ¬ₚ ϕ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; setoid_rewrite pattern_valuation_neg_classic;
    [| typeclasses eauto..].
  by intros Hincl e; apply complement_subseteq_proper, Hincl.
Qed.

Lemma global_semantic_consequence_iff_neg ϕ ψ :
  {ϕ ↔ₚ ψ} ⊧ ¬ₚ ϕ ↔ₚ ¬ₚ ψ.
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; setoid_rewrite pattern_valuation_neg_classic;
    [| typeclasses eauto..].
  by intros Hincl e; apply complement_equiv_proper.
Qed.

Lemma global_semantic_consequence_impl_app_neg_l ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ PApp (¬ₚ ψ) χ →ₚ PApp (¬ₚ ϕ) χ.
Proof.
  etransitivity; [by apply global_semantic_consequence_impl_neg |].
  apply global_semantic_consequence_impl_app_l.
Qed.

Lemma global_semantic_consequence_impl_app_neg_r ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ PApp χ (¬ₚ ψ) →ₚ PApp χ (¬ₚ ϕ).
Proof.
  etransitivity; [by apply global_semantic_consequence_impl_neg |].
  apply global_semantic_consequence_impl_app_r.
Qed.

Lemma global_semantic_consequence_iff_app_neg_l ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ PApp (¬ₚ ϕ) χ ↔ₚ PApp (¬ₚ ψ) χ.
Proof.
  etransitivity; [by apply global_semantic_consequence_iff_neg |].
  apply global_semantic_consequence_iff_app_l.
Qed.

Lemma global_semantic_consequence_iff_app_neg_r ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ PApp χ (¬ₚ ϕ) ↔ₚ PApp χ (¬ₚ ψ).
Proof.
  etransitivity; [by apply global_semantic_consequence_iff_neg |].
  apply global_semantic_consequence_iff_app_r.
Qed.

Lemma set_global_semantic_consequence_impl_app_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ ↔ₚ ψ ->
  Gamma ⊧ PApp χ ϕ ↔ₚ PApp χ ψ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ ↔ₚ ψ ->
  Gamma ⊧ PApp ϕ χ ↔ₚ PApp ψ χ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_neg_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ PApp (¬ₚ ψ) χ →ₚ PApp (¬ₚ ϕ) χ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_neg_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_neg_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ →ₚ ψ ->
  Gamma ⊧ PApp χ (¬ₚ ψ) →ₚ PApp χ (¬ₚ ϕ).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_neg_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_neg_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ ↔ₚ ψ ->
  Gamma ⊧ PApp χ (¬ₚ ϕ) ↔ₚ PApp χ (¬ₚ ψ).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_neg_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_neg_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ ϕ ↔ₚ ψ ->
  Gamma ⊧ PApp (¬ₚ ϕ) χ ↔ₚ PApp (¬ₚ ψ) χ.
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_neg_l.
Qed.

End sec_application.

Section sec_contexts.

Lemma valid_iff_context_bot c :
  csubst c pBot `valid_iff` pBot.
Proof.
  induction c; cbn; [done |..].
  - etransitivity; [| apply valid_iff_app_bot_l].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_l.
  - etransitivity; [| apply valid_iff_app_bot_r].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_r.
Qed.

Lemma valid_iff_context_or c ϕ ψ:
  csubst c (pOr ϕ ψ) `valid_iff` pOr (csubst c ϕ) (csubst c ψ).
Proof.
  induction c; cbn; [done |..].
  - etransitivity; [| apply valid_iff_app_or_l].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_l.
  - etransitivity; [| apply valid_iff_app_or_r].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_r.
Qed.

Lemma valid_iff_context_ex c x ϕ :
  ~ x ∈ CFEV c ->
  csubst c (PEx x ϕ) `valid_iff` PEx x (csubst c ϕ).
Proof.
  intros Hx; induction c; cbn; [done |..].
  - rewrite <- CEVarFree_CFEV in Hx.
    etransitivity;
      [| by apply valid_iff_app_ex_l; contradict Hx; apply cevf_lr, EVarFree_FEV].
    eapply global_semantic_consequence_valid;
      [| by apply IHc; contradict Hx; apply cevf_ll, CEVarFree_CFEV].
    by apply global_semantic_consequence_iff_app_l.
  - rewrite <- CEVarFree_CFEV in Hx.
    etransitivity;
      [| by apply valid_iff_app_ex_r; contradict Hx; apply cevf_rl, EVarFree_FEV].
    eapply global_semantic_consequence_valid;
      [| by apply IHc; contradict Hx; apply cevf_rr, CEVarFree_CFEV].
    by apply global_semantic_consequence_iff_app_r.
Qed.

Lemma valid_impl_context_and c ϕ ψ:
  csubst c (pAnd ϕ ψ) `valid_impl` pAnd (csubst c ϕ) (csubst c ψ).
Proof.
  induction c; cbn; [done |..].
  - etransitivity; [| apply valid_impl_app_and_l].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_impl_app_l.
  - etransitivity; [| apply valid_impl_app_and_r].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_impl_app_r.
Qed.

Lemma valid_impl_context_all c x ϕ :
  ~ x ∈ CFEV c ->
  csubst c (pAll x ϕ) `valid_impl` pAll x (csubst c ϕ).
Proof.
  intros Hx; induction c; cbn; [done |..].
  - rewrite <- CEVarFree_CFEV in Hx.
    etransitivity;
      [| by apply valid_impl_app_all_l; contradict Hx; apply cevf_lr, EVarFree_FEV].
    eapply global_semantic_consequence_valid;
      [| by apply IHc; contradict Hx; apply cevf_ll, CEVarFree_CFEV].
    by apply global_semantic_consequence_impl_app_l.
  - rewrite <- CEVarFree_CFEV in Hx.
    etransitivity;
      [| by apply valid_impl_app_all_r; contradict Hx; apply cevf_rl, EVarFree_FEV].
    eapply global_semantic_consequence_valid;
      [| by apply IHc; contradict Hx; apply cevf_rr, CEVarFree_CFEV].
    by apply global_semantic_consequence_impl_app_r.
Qed.

End sec_contexts.

Section sec_singleton_variables.

Lemma pattern_valuation_context_empty A e c ϕ :
  pattern_valuation A e ϕ ≡ ∅ ->
  pattern_valuation A e (csubst c ϕ) ≡ ∅.
Proof.
  intros Hϕ.
  assert (Hϕ' : esatisfies A e (pIff ϕ pBot)).
  {
    apply esatisfies_iff_classic.
    by rewrite Hϕ, pattern_valuation_bot.
  }
  apply local_semantic_consequence_context_iff with (c := c),
    esatisfies_iff_classic in Hϕ'.
  rewrite Hϕ'.
  transitivity (pattern_valuation A e pBot);
    [| by apply pattern_valuation_bot].
  by apply esatisfies_iff_classic, valid_iff_context_bot.
Qed.

Lemma singleton_valiable_rule c1 c2 x ϕ :
  valid (pNeg (pAnd (csubst c1 (pAnd (PEVar x) ϕ))
    (csubst c2 (pAnd (PEVar x) (pNeg ϕ))))).
Proof.
  intros A e.
  apply top_pattern_valuation_neg_classic; [typeclasses eauto |].
  rewrite pattern_valuation_and_classic by typeclasses eauto.
  destruct (classic (eval e x ∈ pattern_valuation A e ϕ)).
  - rewrite pattern_valuation_context_empty with (c := c2); [set_solver |].
    rewrite pattern_valuation_and_classic, pattern_valuation_neg_classic
      by typeclasses eauto.
    apply elem_of_equiv_empty; intro a.
    rewrite elem_of_intersection, elem_of_complement; set_solver.
  - rewrite pattern_valuation_context_empty with (c := c1); [set_solver |].
    rewrite pattern_valuation_and_classic by typeclasses eauto.
    by cbn; set_solver.
Qed.

End sec_singleton_variables.

Section sec_set_variables.

Lemma global_semantic_consequence_svar_sub0 ϕ ψ X :
  SFreeFor X ψ ϕ ->
  {ϕ} ⊧ svar_sub0 X ψ ϕ.
Proof.
  intros Hfree A Hϕ e.
  unfold esatisfies; rewrite pattern_valuation_svar_sub0 by done.
  by apply Hϕ.
Qed.

Lemma set_global_semantic_consequence_svar_sub0 (Gamma : PatternSet) ϕ ψ X :
  SFreeFor X ψ ϕ ->
  Gamma ⊧ ϕ ->
  Gamma ⊧ svar_sub0 X ψ ϕ.
Proof.
  by intro; apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_svar_sub0.
Qed.

Lemma global_semantic_consequence_ssubst ϕ ψ X :
  {ϕ} ⊧ ssubst ϕ X ψ.
Proof.
  unfold ssubst.
  remember (svar_rename_iter _ _ _) as theta.
  etransitivity; [| apply global_semantic_consequence_svar_sub0].
  - apply globally_logically_equivalent_iff,
      locally_logically_equivalent_global,
      strongly_logically_equivalent_locally,
      strongly_logically_equivalent_valid.
    subst.
    etransitivity;
      [apply valid_svar_rename_iter_fresh | apply valid_evar_rename_iter_fresh];
      [rewrite evar_rename_iter_BSV | rewrite evar_rename_iter_SV |..]; by set_solver.
  - apply SFreeFor_x_theta_if_not_bound.
    + intro y; rewrite EVarFree_FEV, EVarBound_BEV; intro Hy.
      subst.
      rewrite svar_rename_iter_BEV.
      destruct (classic (y ∈ (BEV ϕ ∩ EV ψ))) as [HOcc | Hnocc].
      * apply evar_rename_iter_fresh_not_bound_to_rename; [by set_solver | done].
      * rewrite elem_of_intersection in Hnocc.
        apply not_and_or in Hnocc as [Hnocc | Hnocc];
          [| contradict Hnocc; apply elem_of_union; left; done].
        by apply evar_rename_iter_fresh_not_bound_to_avoid; set_solver.
    + intro y; rewrite SVarFree_FSV, SVarBound_BSV; intros Hy Hny.
      subst.
      destruct (classic (y ∈ (BSV ϕ ∩ SV ψ))) as [HOcc | Hnocc];
        [by apply svar_rename_iter_fresh_not_bound_to_rename; set_solver |].
      apply svar_rename_iter_fresh_not_bound_to_avoid; [| by set_solver].
      by rewrite evar_rename_iter_BSV; set_solver.
Qed.

Lemma set_global_semantic_consequence_ssubst (Gamma : PatternSet) ϕ ψ X :
  Gamma ⊧ ϕ ->
  Gamma ⊧ ssubst ϕ X ψ.
Proof.
  by apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_ssubst.
Qed.

End sec_set_variables.

Section sec_mu.

Lemma global_semantic_consequence_knaster_tarski ϕ ψ X :
  SFreeFor X ψ ϕ ->
  {svar_sub0 X ψ ϕ →ₚ ψ} ⊧ μₚ X ϕ →ₚ ψ.
Proof.
  intro.
  by apply local_semantic_consequence_global,
    local_semantic_consequence_knaster_tarski.
Qed.

Lemma set_global_semantic_consequence_knaster_tarski (Gamma : PatternSet) ϕ ψ X :
  SFreeFor X ψ ϕ ->
  Gamma ⊧ svar_sub0 X ψ ϕ →ₚ ψ ->
  Gamma ⊧ μₚ X ϕ →ₚ ψ.
Proof.
  intro.
  by apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_knaster_tarski.
Qed.

End sec_mu.

End sec_set_global_semantic_consequence.
