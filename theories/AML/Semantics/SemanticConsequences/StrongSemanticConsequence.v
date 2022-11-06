From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import LocalSemanticConsequence.

Section sec_strong_semantic_consequence.

  Context `{signature}.

Definition strong_semantic_consequence (phi psi : Pattern) : Prop :=
  forall s e, pattern_valuation s e phi ⊆ pattern_valuation s e psi.

Definition strongly_logically_equivalent (phi psi : Pattern) : Prop :=
  forall s e, pattern_valuation s e phi ≡ pattern_valuation s e psi.

Lemma strongly_logically_equivalent_iff phi psi :
  strongly_logically_equivalent phi psi
    <->
  strong_semantic_consequence phi psi /\ strong_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intros s e a; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

Lemma strong_semantic_consequence_valid phi psi :
  strong_semantic_consequence phi psi <-> valid (PImpl phi psi).
Proof.
  by unfold valid, satisfies; setoid_rewrite esatisfies_impl_classic.
Qed.

Lemma strongly_logically_equivalent_valid phi psi :
  strongly_logically_equivalent phi psi <-> valid (pIff phi psi).
Proof.
  rewrite valid_iff_alt_classic, <- !strong_semantic_consequence_valid.
  apply strongly_logically_equivalent_iff.
Qed.

#[export] Instance strong_semantic_consequence_valid_classic :
  Proper (strong_semantic_consequence ==> Basics.impl) valid.
Proof.
  intros phi psi; rewrite strong_semantic_consequence_valid.
  by unfold Basics.impl; apply valid_mp_classic.
Qed.

#[export] Instance strongly_logically_equivalent_valid_alt_classic :
  Proper (strongly_logically_equivalent ==> iff) valid.
Proof.
  intros phi psi; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma strong_semantic_consequence_local phi psi :
  strong_semantic_consequence phi psi -> local_semantic_consequence phi psi.
Proof.
  intros Hstrong s e; setoid_rewrite elem_of_equiv_top; intros Hphi a.
  by apply Hstrong, Hphi.
Qed.

Lemma strongly_logically_equivalent_locally phi psi :
  strongly_logically_equivalent phi psi -> locally_logically_equivalent phi psi.
Proof.
  rewrite strongly_logically_equivalent_iff, locally_logically_equivalent_iff.
  by intros []; split; apply strong_semantic_consequence_local.
Qed.

Lemma locally_logically_equivalent_not_strong :
  exists phi psi, locally_logically_equivalent phi psi /\ ~ strong_semantic_consequence phi psi.
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
  exists phi psi, local_semantic_consequence phi psi /\ ~ strong_semantic_consequence phi psi.
Proof.
  destruct locally_logically_equivalent_not_strong as (phi & psi & Heqv & Hncons).
  by exists phi, psi; split; [apply locally_logically_equivalent_iff in Heqv as [] |].
Qed.

Lemma locally_logically_equivalent_not_strongly :
  exists phi psi, locally_logically_equivalent phi psi /\ ~ strongly_logically_equivalent phi psi.
Proof.
  destruct locally_logically_equivalent_not_strong as (phi & psi & Heqv & Hncons).
  exists phi, psi; split; [done |].
  by contradict Hncons; apply strongly_logically_equivalent_iff in Hncons as [].
Qed.

Section sec_set_strong_semantic_consequence.

Context
  `{Set_ Pattern PatternSet}.

Definition set_strong_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s e, set_pattern_valuation s e Gamma ⊆ pattern_valuation s e phi.

#[export] Instance set_strong_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_strong_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_strong_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_strong_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_strong_semantic_consequence.
Proof. by intros Gamma Gamma' Hsub _phi phi -> HGamma' s e; rewrite <- Hsub. Qed.

Lemma set_strong_semantic_consequence_singleton phi psi :
  set_strong_semantic_consequence {[phi]} psi <-> strong_semantic_consequence phi psi.
Proof.
  by unfold set_strong_semantic_consequence; setoid_rewrite set_pattern_valuation_singleton.
Qed.

Lemma set_strong_semantic_consequence_empty_valid phi :
  set_strong_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_strong_semantic_consequence.
  setoid_rewrite set_pattern_valuation_empty_top; [| done].
  by setoid_rewrite top_subseteq_equiv.
Qed.

Lemma set_strong_semantic_consequence_union_left Gamma Gamma' phi :
  set_strong_semantic_consequence Gamma phi ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_strong_semantic_consequence_union_right Gamma Gamma' phi :
  set_strong_semantic_consequence Gamma' phi ->
  set_strong_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_strong_semantic_consequence_any phi Gamma :
  valid phi -> set_strong_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_strong_semantic_consequence_empty_valid.
Qed.

#[export] Instance strong_semantic_consequence_set_consequence Gamma :
  Proper (strong_semantic_consequence ==> Basics.impl) (set_strong_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s e a HGamma; apply Hcns, Hphi. Qed.

#[export] Instance strongly_logically_equivalent_set_consequence Gamma :
  Proper (strongly_logically_equivalent ==> iff) (set_strong_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite strongly_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_strong_semantic_consequence_and Gamma phi psi :
  set_strong_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_strong_semantic_consequence Gamma phi /\ set_strong_semantic_consequence Gamma psi.
Proof.
  unfold set_strong_semantic_consequence.
  setoid_rewrite pattern_valuation_and_classic; [| typeclasses eauto].
  unfold subseteq, set_subseteq_instance.
  setoid_rewrite elem_of_intersection.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_strong_semantic_consequence_iff Gamma phi psi :
  set_strong_semantic_consequence Gamma (pIff phi psi)
    <->
  set_strong_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_strong_semantic_consequence Gamma (PImpl psi phi).
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
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s e a HGamma.
  by apply Hphipsi, Hphi, HDelta.
Qed.

#[export] Instance set_strongly_logically_equivalent_set_consequence_proper :
  Proper (set_strongly_logically_equivalent_set ==> strongly_logically_equivalent ==> iff)
    set_strong_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv.
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
  - by intros Hall _X (phi & -> & Hphi); apply Hall.
  - by intros Hall phi Hphi; apply Hall; eexists.
Qed.

Lemma set_strong_semantic_consequence_local Gamma phi :
  set_strong_semantic_consequence Gamma phi -> set_local_semantic_consequence Gamma phi.
Proof.
  intros Hstrong s e; rewrite set_esatisfies_set_pattern_valuation; setoid_rewrite elem_of_equiv_top.
  by intros HGamma a; apply Hstrong, HGamma.
Qed.

End sec_set_strong_semantic_consequence.

End sec_strong_semantic_consequence.
