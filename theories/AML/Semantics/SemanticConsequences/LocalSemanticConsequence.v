From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From sets Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Tautology.
From AML Require Import StrongSemanticConsequence.

Definition local_semantic_consequence `{signature} (ϕ ψ : Pattern) : Prop :=
  forall s e, esatisfies s e ϕ -> esatisfies s e ψ.

Notation "{ phi } ⊧ₗ psi" := (local_semantic_consequence phi psi) (at level 60, no associativity) : ml_scope.

Definition locally_logically_equivalent `{signature} (ϕ ψ : Pattern) : Prop :=
  forall s e, esatisfies s e ϕ <-> esatisfies s e ψ.

Infix "≡ₗ" := locally_logically_equivalent (at level 60, no associativity) : ml_scope.

Section sec_local_semantic_consequence.

Context `{signature}.

#[export] Instance local_semantic_consequence_refl : Reflexive local_semantic_consequence.
Proof. by intros ? ?. Qed.

#[export] Instance local_semantic_consequence_trans : Transitive local_semantic_consequence.
Proof.
  intros ϕ ψ χ Hψ Hchi s e Hϕ.
  by apply Hchi, Hψ.
Qed.

#[export] Instance locally_logically_equivalent_refl : Reflexive locally_logically_equivalent.
Proof. by intros ? ?. Qed.

#[export] Instance locally_logically_equivalent_trans : Transitive locally_logically_equivalent.
Proof.
  intros ϕ ψ χ Hψ Hchi s e.
  by etransitivity; [apply Hψ | apply Hchi].
Qed.

#[export] Instance locally_logically_equivalent_sym : Symmetric locally_logically_equivalent.
Proof.
  intros ϕ ψ Hψ s e.
  by symmetry.
Qed.

Lemma locally_logically_equivalent_iff ϕ ψ :
  ϕ ≡ₗ ψ
    <->
  {ϕ} ⊧ₗ ψ /\ {ψ} ⊧ₗ ϕ.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance local_semantic_consequence_esatisfies s e :
  Proper (local_semantic_consequence ==> Basics.impl) (esatisfies s e).
Proof. intros ϕ ψ Hcns Hϕ; apply Hcns, Hϕ. Qed.

#[export] Instance local_semantic_consequence_valid :
  Proper (local_semantic_consequence ==> Basics.impl) valid.
Proof. by intros ϕ ψ Hcns Hϕ s e; apply Hcns, Hϕ. Qed.

#[export] Instance locally_logically_equivalent_satisfies s e :
  Proper (locally_logically_equivalent ==> iff) (esatisfies s e).
Proof.
  intros ϕ ψ; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance locally_logically_equivalent_valid :
  Proper (locally_logically_equivalent ==> iff) valid.
Proof.
  intros ϕ ψ; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma locally_logically_equivalent_evar x y :
  PEVar x ≡ₗ PEVar y.
Proof. by intros s e; rewrite !esatisfies_evar. Qed.

Lemma strong_semantic_consequence_local ϕ ψ :
  {ϕ} ⊧ₛ ψ -> {ϕ} ⊧ₗ ψ.
Proof.
  intros Hstrong s e; setoid_rewrite elem_of_equiv_top; intros Hϕ a.
  by apply Hstrong, Hϕ.
Qed.

Lemma strongly_logically_equivalent_locally ϕ ψ :
  ϕ ≡ₛ ψ -> ϕ ≡ₗ ψ.
Proof.
  rewrite strongly_logically_equivalent_iff, locally_logically_equivalent_iff.
  by intros []; split; apply strong_semantic_consequence_local.
Qed.

Lemma locally_logically_equivalent_not_strong :
  exists ϕ ψ, ϕ ≡ₗ ψ /\ ~ {ϕ} ⊧ₛ ψ.
Proof.
  assert (exists x y : EVar, x <> y) as (x & y & Hxy).
  {
    pose (x := fresh [] : EVar ).
    exists x, (fresh [x]).
    intro Hx.
    by apply infinite_is_fresh with [x], elem_of_list_singleton.
  }
  exists (PEVar x), (PEVar y); split.
  - by apply locally_logically_equivalent_evar.
  - intro Hlocal.
    pose (s := {| idomain := EVar; non_empty := populate x;
                  iapp := fun x y z => False; isigma := fun x y => False |}).
    assert (exists (e : Valuation), ¬ pattern_valuation s e (PEVar x) ⊆  pattern_valuation s e (PEVar y))
      as (e & Hne).
    {
      unshelve esplit; [split; [exact id | exact (const ∅)] |].
      cbn; contradict Hxy.
      pose (@pow_set_semiset idomain).
      by eapply @elem_of_singleton, Hxy, elem_of_singleton.
    }
    by contradict Hne; apply Hlocal.
Qed.

Lemma local_semantic_consequence_not_strong :
  exists ϕ ψ, {ϕ} ⊧ₗ ψ /\ ~ {ϕ} ⊧ₛ ψ.
Proof.
  destruct locally_logically_equivalent_not_strong as (ϕ & ψ & Heqv & Hncons).
  by exists ϕ, ψ; split; [apply locally_logically_equivalent_iff in Heqv as [] |].
Qed.

Lemma locally_logically_equivalent_not_strongly :
  exists ϕ ψ, ϕ ≡ₗ ψ /\ ~ ϕ ≡ₛ ψ.
Proof.
  destruct locally_logically_equivalent_not_strong as (ϕ & ψ & Heqv & Hncons).
  exists ϕ, ψ; split; [done |].
  by contradict Hncons; apply strongly_logically_equivalent_iff in Hncons as [].
Qed.

End sec_local_semantic_consequence.

Section sec_set_local_semantic_consequence_definition.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Definition set_local_semantic_consequence (Gamma : PatternSet) (ϕ : Pattern) :=
  forall s e, set_esatisfies s e Gamma -> esatisfies s e ϕ.

#[export] Instance set_local_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _ϕ ϕ ->.
  by unfold set_local_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_local_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _ϕ ϕ -> HGamma' s e HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_local_semantic_consequence_singleton ϕ ψ :
  set_local_semantic_consequence {[ϕ]} ψ <-> {ϕ} ⊧ₗ ψ.
Proof.
  unfold set_local_semantic_consequence, local_semantic_consequence.
  by setoid_rewrite set_esatisfies_singleton.
Qed.

Lemma set_local_semantic_consequence_empty_valid ϕ :
  set_local_semantic_consequence ∅ ϕ <-> valid ϕ.
Proof.
  unfold set_local_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intros Hempty e; apply Hempty; intros _ϕ H_ϕ.
  contradict H_ϕ; apply not_elem_of_empty.
Qed.

End sec_set_local_semantic_consequence_definition.

Infix "⊧ₗ" := set_local_semantic_consequence (at level 60, no associativity) : ml_scope.

Section sec_set_local_semantic_consequence.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Lemma set_local_semantic_consequence_union_left (Gamma Gamma' : PatternSet) ϕ :
  Gamma ⊧ₗ ϕ ->
  Gamma ∪ Gamma' ⊧ₗ ϕ.
Proof.
  intros HGamma.
  eapply set_local_semantic_consequence_proper_subseteq; [| done..].
  by eapply union_subseteq_l.
Qed.

Lemma set_local_semantic_consequence_union_right (Gamma Gamma' : PatternSet) ϕ :
  Gamma' ⊧ₗ ϕ ->
  Gamma ∪ Gamma' ⊧ₗ ϕ.
Proof.
  intros HGamma.
  eapply set_local_semantic_consequence_proper_subseteq; [| done..].
  by eapply union_subseteq_r.
Qed.

Lemma set_strong_semantic_consequence_local (Gamma : PatternSet) ϕ :
  Gamma ⊧ₛ ϕ -> Gamma ⊧ₗ ϕ.
Proof.
  intros Hstrong s e; rewrite set_esatisfies_set_pattern_valuation; setoid_rewrite elem_of_equiv_top.
  by intros HGamma a; apply Hstrong, HGamma.
Qed.

Lemma valid_set_local_semantic_consequence_any ϕ (Gamma : PatternSet) :
  valid ϕ -> Gamma ⊧ₗ ϕ.
Proof.
  by intro; apply set_strong_semantic_consequence_local,
    valid_set_strong_semantic_consequence_any.
Qed.

#[export] Instance local_semantic_consequence_set_consequence (Gamma : PatternSet) :
  Proper (local_semantic_consequence ==> Basics.impl) (set_local_semantic_consequence Gamma).
Proof. by intros ϕ ψ Hcns Hϕ s e HGamma; apply Hcns, Hϕ. Qed.

#[export] Instance locally_logically_equivalent_set_consequence (Gamma : PatternSet) :
  Proper (locally_logically_equivalent ==> iff) (set_local_semantic_consequence Gamma).
Proof.
  intros ϕ ψ; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_local_semantic_consequence_and (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ₗ ϕ ∧ₚ ψ
    <->
  Gamma ⊧ₗ ϕ /\ Gamma ⊧ₗ ψ.
Proof.
  unfold set_local_semantic_consequence.
  setoid_rewrite esatisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_local_semantic_consequence_iff (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ
    <->
  Gamma ⊧ₗ ϕ →ₚ ψ /\ Gamma ⊧ₗ ψ →ₚ ϕ.
Proof.
  unfold set_local_semantic_consequence; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_local_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation), set_esatisfies s e Gamma -> set_esatisfies s e Delta.

Infix "|=ₗ" := set_local_semantic_consequence_set (at level 60, no associativity) : ml_scope.

#[export] Instance set_local_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_local_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_local_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_local_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_local_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_local_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_local_semantic_consequence_set_satisfies_proper s e :
  Proper (set_local_semantic_consequence_set ==> Basics.impl) (set_esatisfies s e).
Proof. by intros Gamma Delta HGammaDelta HGamma; apply HGammaDelta. Qed.

Definition set_locally_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation),
    set_esatisfies s e Gamma <-> set_esatisfies s e Delta.

#[export] Instance set_locally_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_locally_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_locally_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_locally_logically_equivalent_set_proper_iff Gamma Delta :
  set_locally_logically_equivalent_set Gamma Delta
    <->
  Gamma |=ₗ Delta /\ Delta |=ₗ Gamma .
Proof.
  unfold set_locally_logically_equivalent_set, set_local_semantic_consequence_set.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_locally_logically_equivalent_set_set_satisfies_proper s e :
  Proper (set_locally_logically_equivalent_set ==> iff) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_locally_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_local_semantic_consequence_set_consequence_proper :
  Proper (set_local_semantic_consequence_set --> locally_logically_equivalent ==> Basics.impl)
    set_local_semantic_consequence.
Proof.
  intros Delta Gamma HDelta ϕ ψ Hϕψ Hϕ s e HGamma.
  by rewrite <- Hϕψ; apply Hϕ; rewrite HDelta.
Qed.

#[export] Instance set_locally_logically_equivalent_set_consequence_proper :
  Proper (set_locally_logically_equivalent_set ==> locally_logically_equivalent ==> iff)
    set_local_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv ϕ ψ Heqv; unfold set_local_semantic_consequence.
  by setoid_rewrite Hset_eqv; setoid_rewrite Heqv.
Qed.

Lemma set_locally_logically_equivalent_set_finite_classic
  `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_locally_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intros s e.
  rewrite set_esatisfies_singleton, esatisfies_finite_conjunction_classic, Forall_forall by done.
  unfold set_esatisfies, esatisfies.
  setoid_rewrite elem_of_elements.
  itauto.
Qed.

Section sec_rules.

Lemma set_local_mp (Gamma : PatternSet) ϕ ψ :
  Gamma ⊧ₗ ϕ ->
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ ψ.
Proof.
  intros Hϕ Hϕψ A e HGamma.
  specialize (Hϕ A e HGamma).
  specialize (Hϕψ A e HGamma).
  by eapply esatisfies_mp_classic.
Qed.

Lemma set_local_impl_trans (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ ψ →ₚ χ ->
  Gamma ⊧ₗ ψ →ₚ χ.
Proof.
  intros Hϕψ Hψchi A e HGamma.
  specialize (Hϕψ A e HGamma).
  specialize (Hψchi A e HGamma).
  rewrite esatisfies_impl_classic in Hϕψ, Hψchi |- *.
  by etransitivity.
Qed.

Lemma set_local_and_curry (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ ∧ₚ ψ →ₚ χ
    <->
  Gamma ⊧ₗ ϕ →ₚ ψ →ₚ χ.
Proof.
  pose proof (Hcurry := tautology_impl_impl_and ϕ ψ χ).
  apply tautology_valid, strongly_logically_equivalent_valid, strongly_logically_equivalent_locally in Hcurry.
  by rewrite Hcurry.
Qed.

End sec_rules.

Section sec_application.

Lemma local_semantic_consequence_impl_app_r ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ₗ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  intros A e; rewrite !esatisfies_impl_classic; cbn.
  by intros Hincl; rewrite Hincl.
Qed.

Lemma local_semantic_consequence_impl_app_l ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ₗ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  intros A e; rewrite !esatisfies_impl_classic; cbn.
  by intros Hincl; rewrite Hincl.
Qed.

Lemma local_semantic_consequence_iff_app_r ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ₗ PApp χ ϕ ↔ₚ PApp χ ψ.
Proof.
  intros A e; rewrite !esatisfies_iff_classic; cbn.
  by intros Hincl; rewrite Hincl.
Qed.

Lemma local_semantic_consequence_iff_app_l ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ₗ PApp ϕ χ ↔ₚ PApp ψ χ.
Proof.
  intros A e; rewrite !esatisfies_iff_classic; cbn.
  by intros Hincl; rewrite Hincl.
Qed.

Lemma local_semantic_consequence_impl_neg ϕ ψ :
  {ϕ →ₚ ψ} ⊧ₗ ¬ₚ ψ →ₚ ¬ₚ ϕ.
Proof.
  intros A e; rewrite !esatisfies_impl_classic, !pattern_valuation_neg_classic
    by typeclasses eauto.
  by apply complement_subseteq_proper.
Qed.

Lemma local_semantic_consequence_iff_neg ϕ ψ :
  {ϕ ↔ₚ ψ} ⊧ₗ ¬ₚ ϕ ↔ₚ ¬ₚ ψ.
Proof.
  intros A e; rewrite !esatisfies_iff_classic, !pattern_valuation_neg_classic
    by typeclasses eauto.
  by apply complement_equiv_proper.
Qed.

Lemma local_semantic_consequence_impl_app_neg_l ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ₗ PApp (¬ₚ ψ) χ →ₚ PApp (¬ₚ ϕ) χ.
Proof.
  etransitivity; [by apply local_semantic_consequence_impl_neg |].
  apply local_semantic_consequence_impl_app_l.
Qed.

Lemma local_semantic_consequence_impl_app_neg_r ϕ ψ χ :
  {ϕ →ₚ ψ} ⊧ₗ PApp χ (¬ₚ ψ) →ₚ PApp χ (¬ₚ ϕ).
Proof.
  etransitivity; [by apply local_semantic_consequence_impl_neg |].
  apply local_semantic_consequence_impl_app_r.
Qed.

Lemma local_semantic_consequence_iff_app_neg_l ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ₗ PApp (¬ₚ ϕ) χ ↔ₚ PApp (¬ₚ ψ) χ.
Proof.
  etransitivity; [by apply local_semantic_consequence_iff_neg |].
  apply local_semantic_consequence_iff_app_l.
Qed.

Lemma local_semantic_consequence_iff_app_neg_r ϕ ψ χ :
  {ϕ ↔ₚ ψ} ⊧ₗ PApp χ (¬ₚ ϕ) ↔ₚ PApp χ (¬ₚ ψ).
Proof.
  etransitivity; [by apply local_semantic_consequence_iff_neg |].
  apply local_semantic_consequence_iff_app_r.
Qed.

Lemma set_local_semantic_consequence_impl_app_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_impl_app_l.
Qed.

Lemma set_local_semantic_consequence_impl_app_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_impl_app_r.
Qed.

Lemma set_local_semantic_consequence_iff_app_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ ->
  Gamma ⊧ₗ PApp χ ϕ ↔ₚ PApp χ ψ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_iff_app_r.
Qed.

Lemma set_local_semantic_consequence_iff_app_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ ->
  Gamma ⊧ₗ PApp ϕ χ ↔ₚ PApp ψ χ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_iff_app_l.
Qed.

Lemma set_local_semantic_consequence_impl_app_neg_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ PApp (¬ₚ ψ) χ →ₚ PApp (¬ₚ ϕ) χ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_impl_app_neg_l.
Qed.

Lemma set_local_semantic_consequence_impl_app_neg_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ PApp χ (¬ₚ ψ) →ₚ PApp χ (¬ₚ ϕ).
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_impl_app_neg_r.
Qed.

Lemma set_local_semantic_consequence_iff_app_neg_elim_r (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ ->
  Gamma ⊧ₗ PApp χ (¬ₚ ϕ) ↔ₚ PApp χ (¬ₚ ψ).
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_iff_app_neg_r.
Qed.

Lemma set_local_semantic_consequence_iff_app_neg_elim_l (Gamma : PatternSet) ϕ ψ χ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ ->
  Gamma ⊧ₗ PApp (¬ₚ ϕ) χ ↔ₚ PApp (¬ₚ ψ) χ.
Proof.
  apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_iff_app_neg_l.
Qed.

End sec_application.

Section sec_contexts.

Lemma local_semantic_consequence_context_impl c ϕ ψ :
  {ϕ →ₚ ψ} ⊧ₗ csubst c ϕ →ₚ csubst c ψ.
Proof.
  intros A e; induction c; cbn; [done |..]; intros Himpl.
  - by apply local_semantic_consequence_impl_app_l, IHc.
  - by apply local_semantic_consequence_impl_app_r, IHc.
Qed.

Lemma local_semantic_consequence_context_iff c ϕ ψ :
  {ϕ ↔ₚ ψ} ⊧ₗ csubst c ϕ ↔ₚ csubst c ψ.
Proof.
  intros A e; induction c; cbn; [done |..]; intros Himpl.
  - by apply local_semantic_consequence_iff_app_l, IHc.
  - by apply local_semantic_consequence_iff_app_r, IHc.
Qed.

Lemma set_local_semantic_consequence_context_impl (Gamma : PatternSet) c ϕ ψ :
  Gamma ⊧ₗ ϕ →ₚ ψ ->
  Gamma ⊧ₗ csubst c ϕ →ₚ csubst c ψ.
Proof.
  intros Himpl A e HGamma.
  by apply local_semantic_consequence_context_impl, Himpl.
Qed.

Lemma set_local_semantic_consequence_context_iff (Gamma : PatternSet) c ϕ ψ :
  Gamma ⊧ₗ ϕ ↔ₚ ψ ->
  Gamma ⊧ₗ csubst c ϕ ↔ₚ csubst c ψ.
Proof.
  intros Hiff A e HGamma.
  by apply local_semantic_consequence_context_iff, Hiff.
Qed.

End sec_contexts.

Section sec_mu.

Lemma local_semantic_consequence_knaster_tarski ϕ ψ X :
  SFreeFor X ψ ϕ ->
  {svar_sub0 X ψ ϕ →ₚ ψ} ⊧ₗ μₚ X ϕ →ₚ ψ.
Proof.
  intros ? A e; rewrite !esatisfies_impl_classic.
  rewrite pattern_valuation_svar_sub0 by done.
  intros Hincl; cbn.
  apply (member_of_filtered_intersection (λ B : Ensemble idomain,
  pattern_valuation A (valuation_supdate e X B) ϕ ⊆ B) id _ Hincl).
Qed.

Lemma set_local_semantic_consequence_knaster_tarski (Gamma : PatternSet) ϕ ψ X :
  SFreeFor X ψ ϕ ->
  Gamma ⊧ₗ svar_sub0 X ψ ϕ →ₚ ψ ->
  Gamma ⊧ₗ μₚ X ϕ →ₚ ψ.
Proof.
  intro.
  by apply local_semantic_consequence_set_consequence,
    local_semantic_consequence_knaster_tarski.
Qed.

End sec_mu.

End sec_set_local_semantic_consequence.
