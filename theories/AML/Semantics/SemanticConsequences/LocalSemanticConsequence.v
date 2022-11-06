From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Tautology.
From AML Require Import StrongSemanticConsequence.

Section sec_local_semantic_consequence.

  Context `{signature}.

Definition local_semantic_consequence (phi psi : Pattern) : Prop :=
  forall s e, esatisfies s e phi -> esatisfies s e psi.

Definition locally_logically_equivalent (phi psi : Pattern) : Prop :=
  forall s e, esatisfies s e phi <-> esatisfies s e psi.

Lemma locally_logically_equivalent_iff phi psi :
  locally_logically_equivalent phi psi
    <->
  local_semantic_consequence phi psi /\ local_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance local_semantic_consequence_esatisfies s e :
  Proper (local_semantic_consequence ==> Basics.impl) (esatisfies s e).
Proof. intros phi psi Hcns Hphi; apply Hcns, Hphi. Qed.

#[export] Instance local_semantic_consequence_valid :
  Proper (local_semantic_consequence ==> Basics.impl) valid.
Proof. by intros phi psi Hcns Hphi s e; apply Hcns, Hphi. Qed.

#[export] Instance locally_logically_equivalent_satisfies s e :
  Proper (locally_logically_equivalent ==> iff) (esatisfies s e).
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance locally_logically_equivalent_valid :
  Proper (locally_logically_equivalent ==> iff) valid.
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma locally_logically_equivalent_evar x y :
  locally_logically_equivalent (PEVar x) (PEVar y).
Proof. by intros s e; rewrite !esatisfies_evar. Qed.

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

Section sec_set_local_semantic_consequence.

Context
  `{Set_ Pattern PatternSet}.

Definition set_local_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s e, set_esatisfies s e Gamma -> esatisfies s e phi.

#[export] Instance set_local_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_local_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_local_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_local_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _phi phi -> HGamma' s e HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_local_semantic_consequence_singleton phi psi :
  set_local_semantic_consequence {[phi]} psi <-> local_semantic_consequence phi psi.
Proof.
  unfold set_local_semantic_consequence, local_semantic_consequence.
  by setoid_rewrite set_esatisfies_singleton.
Qed.

Lemma set_local_semantic_consequence_empty_valid phi :
  set_local_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_local_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intros Hempty e; apply Hempty; intros _phi H_phi.
  contradict H_phi; apply not_elem_of_empty.
Qed.

Lemma set_local_semantic_consequence_union_left Gamma Gamma' phi :
  set_local_semantic_consequence Gamma phi ->
  set_local_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_local_semantic_consequence_union_right Gamma Gamma' phi :
  set_local_semantic_consequence Gamma' phi ->
  set_local_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_local_semantic_consequence_any phi Gamma :
  valid phi -> set_local_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_local_semantic_consequence_empty_valid.
Qed.

#[export] Instance local_semantic_consequence_set_consequence Gamma :
  Proper (local_semantic_consequence ==> Basics.impl) (set_local_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s e HGamma; apply Hcns, Hphi. Qed.

#[export] Instance locally_logically_equivalent_set_consequence Gamma :
  Proper (locally_logically_equivalent ==> iff) (set_local_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite locally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_local_semantic_consequence_and Gamma phi psi :
  set_local_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_local_semantic_consequence Gamma phi /\ set_local_semantic_consequence Gamma psi.
Proof.
  unfold set_local_semantic_consequence.
  setoid_rewrite esatisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_local_semantic_consequence_iff Gamma phi psi :
  set_local_semantic_consequence Gamma (pIff phi psi)
    <->
  set_local_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_local_semantic_consequence Gamma (PImpl psi phi).
Proof.
  unfold set_local_semantic_consequence; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_local_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure) (e : Valuation), set_esatisfies s e Gamma -> set_esatisfies s e Delta.

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
  set_local_semantic_consequence_set Gamma Delta /\ set_local_semantic_consequence_set Delta Gamma .
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
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s e HGamma.
  by rewrite <- Hphipsi; apply Hphi; rewrite HDelta.
Qed.

#[export] Instance set_locally_logically_equivalent_set_consequence_proper :
  Proper (set_locally_logically_equivalent_set ==> locally_logically_equivalent ==> iff)
    set_local_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv; unfold set_local_semantic_consequence.
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

Lemma set_strong_semantic_consequence_local Gamma phi :
  set_strong_semantic_consequence Gamma phi -> set_local_semantic_consequence Gamma phi.
Proof.
  intros Hstrong s e; rewrite set_esatisfies_set_pattern_valuation; setoid_rewrite elem_of_equiv_top.
  by intros HGamma a; apply Hstrong, HGamma.
Qed.

Section sec_rules.

Lemma set_local_mp Gamma phi psi :
  set_local_semantic_consequence Gamma phi ->
  set_local_semantic_consequence Gamma (PImpl phi psi) ->
  set_local_semantic_consequence Gamma psi.
Proof.
  intros Hphi Hphipsi A e HGamma.
  specialize (Hphi A e HGamma).
  specialize (Hphipsi A e HGamma).
  by eapply esatisfies_mp_classic.
Qed.

Lemma set_local_impl_trans Gamma phi psi chi :
  set_local_semantic_consequence Gamma (PImpl phi psi) ->
  set_local_semantic_consequence Gamma (PImpl psi chi) ->
  set_local_semantic_consequence Gamma (PImpl psi chi).
Proof.
  intros Hphipsi Hpsichi A e HGamma.
  specialize (Hphipsi A e HGamma).
  specialize (Hpsichi A e HGamma).
  rewrite esatisfies_impl_classic in Hphipsi, Hpsichi |- *.
  by etransitivity.
Qed.

Lemma set_local_and_curry Gamma phi psi chi :
  set_local_semantic_consequence Gamma (PImpl (pAnd phi psi) chi)
    <->
  set_local_semantic_consequence Gamma (PImpl phi (PImpl psi chi)).
Proof.
  pose proof (Hcurry := tautology_impl_impl_and phi psi chi).
  apply tautology_valid, strongly_logically_equivalent_valid, strongly_logically_equivalent_locally in Hcurry.
  by rewrite Hcurry.
Qed.

End sec_rules.

End sec_set_local_semantic_consequence.

End sec_local_semantic_consequence.
