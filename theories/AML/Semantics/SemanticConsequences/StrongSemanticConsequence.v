From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Tautology.

Section sec_strong_semantic_consequence.

  Context `{signature}.

Definition strong_semantic_consequence (ϕ ψ : Pattern) : Prop :=
  forall s e, pattern_valuation s e ϕ ⊆ pattern_valuation s e ψ.

Definition strongly_logically_equivalent (ϕ ψ : Pattern) : Prop :=
  forall s e, pattern_valuation s e ϕ ≡ pattern_valuation s e ψ.

#[export] Instance strongly_logically_equivalent_refl :
  Reflexive strongly_logically_equivalent.
Proof. done. Qed.

#[export] Instance strongly_logically_equivalent_trans :
  Transitive strongly_logically_equivalent.
Proof.
  intros ϕ ψ χ Hϕψ Hψchi A e.
  specialize (Hϕψ A e).
  specialize (Hψchi A e).
  by etransitivity.
Qed.

#[export] Instance strongly_logically_equivalent_sym :
  Symmetric strongly_logically_equivalent.
Proof.
  intros ϕ ψ Hϕψ A e.
  by symmetry; apply Hϕψ.
Qed.

Lemma strongly_logically_equivalent_iff ϕ ψ :
  strongly_logically_equivalent ϕ ψ
    <->
  strong_semantic_consequence ϕ ψ /\ strong_semantic_consequence ψ ϕ.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intros s e a; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

Lemma strong_semantic_consequence_valid ϕ ψ :
  strong_semantic_consequence ϕ ψ <-> ϕ `valid_impl` ψ.
Proof.
  by unfold valid_impl, valid, satisfies; setoid_rewrite esatisfies_impl_classic.
Qed.

Lemma strongly_logically_equivalent_valid ϕ ψ :
  strongly_logically_equivalent ϕ ψ <-> ϕ `valid_iff` ψ.
Proof.
  rewrite valid_iff_alt_classic, <- !strong_semantic_consequence_valid.
  apply strongly_logically_equivalent_iff.
Qed.

#[export] Instance strong_semantic_consequence_valid_classic :
  Proper (strong_semantic_consequence ==> Basics.impl) valid.
Proof.
  intros ϕ ψ; rewrite strong_semantic_consequence_valid.
  by unfold Basics.impl; apply valid_mp_classic.
Qed.

#[export] Instance strongly_logically_equivalent_valid_alt_classic :
  Proper (strongly_logically_equivalent ==> iff) valid.
Proof.
  intros ϕ ψ; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Section sec_set_strong_semantic_consequence.

Context
  `{Set_ Pattern PatternSet}.

Definition set_strong_semantic_consequence (Gamma : PatternSet) (ϕ : Pattern) :=
  forall s e, set_pattern_valuation s e Gamma ⊆ pattern_valuation s e ϕ.

#[export] Instance set_strong_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_strong_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _ϕ ϕ ->.
  by unfold set_strong_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_strong_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_strong_semantic_consequence.
Proof. by intros Gamma Gamma' Hsub _ϕ ϕ -> HGamma' s e; rewrite <- Hsub. Qed.

Lemma set_strong_semantic_consequence_singleton ϕ ψ :
  set_strong_semantic_consequence {[ϕ]} ψ <-> strong_semantic_consequence ϕ ψ.
Proof.
  by unfold set_strong_semantic_consequence; setoid_rewrite set_pattern_valuation_singleton.
Qed.

Lemma set_strong_semantic_consequence_empty_valid ϕ :
  set_strong_semantic_consequence ∅ ϕ <-> valid ϕ.
Proof.
  unfold set_strong_semantic_consequence.
  setoid_rewrite set_pattern_valuation_empty_top; [| done].
  by setoid_rewrite top_subseteq_equiv.
Qed.

Lemma set_strong_semantic_consequence_union_left Gamma Gamma' ϕ :
  set_strong_semantic_consequence Gamma ϕ ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') ϕ.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_strong_semantic_consequence_union_right Gamma Gamma' ϕ :
  set_strong_semantic_consequence Gamma' ϕ ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') ϕ.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_strong_semantic_consequence_any ϕ Gamma :
  valid ϕ -> set_strong_semantic_consequence Gamma ϕ.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_strong_semantic_consequence_empty_valid.
Qed.

#[export] Instance strong_semantic_consequence_set_consequence Gamma :
  Proper (strong_semantic_consequence ==> Basics.impl) (set_strong_semantic_consequence Gamma).
Proof. by intros ϕ ψ Hcns Hϕ s e a HGamma; apply Hcns, Hϕ. Qed.

#[export] Instance strongly_logically_equivalent_set_consequence Gamma :
  Proper (strongly_logically_equivalent ==> iff) (set_strong_semantic_consequence Gamma).
Proof.
  intros ϕ ψ; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_strong_semantic_consequence_and Gamma ϕ ψ :
  set_strong_semantic_consequence Gamma (pAnd ϕ ψ)
    <->
  set_strong_semantic_consequence Gamma ϕ /\ set_strong_semantic_consequence Gamma ψ.
Proof.
  unfold set_strong_semantic_consequence.
  setoid_rewrite pattern_valuation_and_classic; [| typeclasses eauto].
  unfold subseteq, set_subseteq_instance.
  setoid_rewrite elem_of_intersection.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_strong_semantic_consequence_iff Gamma ϕ ψ :
  set_strong_semantic_consequence Gamma (pIff ϕ ψ)
    <->
  set_strong_semantic_consequence Gamma (PImpl ϕ ψ)
    /\
  set_strong_semantic_consequence Gamma (PImpl ψ ϕ).
Proof. by unfold pIff; rewrite set_strong_semantic_consequence_and. Qed.

Definition set_strong_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation),
    set_pattern_valuation s e Gamma ⊆ set_pattern_valuation s e Delta.

#[export] Instance set_strong_semantic_consequence_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_strong_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strong_semantic_consequence_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_strong_semantic_consequence_set_proper_subseteq :
  Proper ((⊆) ==> (⊆) --> Basics.impl) set_strong_semantic_consequence_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strong_semantic_consequence_set.
  by setoid_rewrite <- HGamma; setoid_rewrite HDelta.
Qed.

#[export] Instance set_strong_semantic_consequence_set_satisfies_proper s e :
  Proper (set_strong_semantic_consequence_set ==> Basics.impl) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  rewrite !set_esatisfies_set_pattern_valuation, !elem_of_equiv_top.
  by intros HGamma a; apply HGammaDelta, HGamma.
Qed.

Definition set_strongly_logically_equivalent_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation),
    set_pattern_valuation s e Gamma ≡ set_pattern_valuation s e Delta.

#[export] Instance set_strongly_logically_equivalent_set_proper :
  Proper ((≡) ==> (≡) ==> iff) set_strongly_logically_equivalent_set.
Proof.
  intros Gamma Gamma' HGamma Delta Delta' HDelta.
  unfold set_strongly_logically_equivalent_set.
  by setoid_rewrite HGamma; setoid_rewrite HDelta.
Qed.

Lemma set_strongly_logically_equivalent_set_proper_iff Gamma Delta :
  set_strongly_logically_equivalent_set Gamma Delta
    <->
  set_strong_semantic_consequence_set Gamma Delta /\ set_strong_semantic_consequence_set Delta Gamma .
Proof.
  unfold set_strongly_logically_equivalent_set, set_strong_semantic_consequence_set.
  setoid_rewrite set_equiv_subseteq.
  by split; [intros Heqv; split; intros; apply Heqv | intros []; split; auto].
Qed.

#[export] Instance set_strongly_logically_equivalent_set_set_satisfies_proper s e :
  Proper (set_strongly_logically_equivalent_set ==> iff) (set_esatisfies s e).
Proof.
  intros Gamma Delta HGammaDelta.
  apply set_strongly_logically_equivalent_set_proper_iff in HGammaDelta as [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance set_strong_semantic_consequence_set_consequence_proper :
  Proper (set_strong_semantic_consequence_set --> strongly_logically_equivalent ==> Basics.impl)
    set_strong_semantic_consequence.
Proof.
  intros Delta Gamma HDelta ϕ ψ Hϕψ Hϕ s e a HGamma.
  by apply Hϕψ, Hϕ, HDelta.
Qed.

#[export] Instance set_strongly_logically_equivalent_set_consequence_proper :
  Proper (set_strongly_logically_equivalent_set ==> strongly_logically_equivalent ==> iff)
    set_strong_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv ϕ ψ Heqv.
  do 3 (apply forall_proper; intro).
  by split; intros Hsat ?; apply Heqv, Hsat, Hset_eqv.
Qed.

Lemma set_strongly_logically_equivalent_set_finite_classic
    `{!Elements Pattern PatternSet} `{!FinSet Pattern PatternSet} (Gamma : PatternSet) :
  set_strongly_logically_equivalent_set Gamma {[finite_conjunction (elements Gamma)]}.
Proof.
  intros s e.
  rewrite set_pattern_valuation_singleton, pattern_valuation_finite_conjunction_classic
    by typeclasses eauto.
  intro a; rewrite elem_of_set_pattern_valuation, elem_of_intersection_list.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_elements.
  split.
  - by intros Hall _X (ϕ & -> & Hϕ); apply Hall.
  - by intros Hall ϕ Hϕ; apply Hall; eexists.
Qed.

Section sec_rules.

Lemma set_strong_mp Gamma ϕ ψ :
  set_strong_semantic_consequence Gamma ϕ ->
  set_strong_semantic_consequence Gamma (PImpl ϕ ψ) ->
  set_strong_semantic_consequence Gamma ψ.
Proof.
  intros Hϕ Hϕψ A e.
  transitivity (pattern_valuation A e ϕ ∩ pattern_valuation A e (PImpl ϕ ψ));
    [specialize (Hϕ A e); specialize (Hϕψ A e); set_solver |].
  rewrite pattern_valuation_impl_alt_classic by typeclasses eauto.
  intro a; rewrite elem_of_intersection, elem_of_union, elem_of_complement.
  by set_solver.
Qed.

Lemma set_strong_impl_trans Gamma ϕ ψ χ :
  set_strong_semantic_consequence Gamma (PImpl ϕ ψ) ->
  set_strong_semantic_consequence Gamma (PImpl ψ χ) ->
  set_strong_semantic_consequence Gamma (PImpl ψ χ).
Proof.
  intros Hϕψ Hψchi A e.
  transitivity (pattern_valuation A e (PImpl ϕ ψ) ∩ pattern_valuation A e (PImpl ψ χ));
    [specialize (Hϕψ A e); specialize (Hψchi A e); set_solver |].
  rewrite !pattern_valuation_impl_alt_classic by typeclasses eauto.
  by set_solver.
Qed.

Lemma set_strong_and_curry Gamma ϕ ψ χ :
  set_strong_semantic_consequence Gamma (PImpl (pAnd ϕ ψ) χ)
    <->
  set_strong_semantic_consequence Gamma (PImpl ϕ (PImpl ψ χ)).
Proof.
  pose proof (Hcurry := tautology_impl_impl_and ϕ ψ χ).
  apply tautology_valid, strongly_logically_equivalent_valid in Hcurry.
  by rewrite Hcurry.
Qed.

End sec_rules.

End sec_set_strong_semantic_consequence.

End sec_strong_semantic_consequence.
