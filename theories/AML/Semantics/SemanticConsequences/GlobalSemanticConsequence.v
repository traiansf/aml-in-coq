From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.

Section sec_global_semantic_consequence.

  Context `{signature}.

Definition global_semantic_consequence (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi -> satisfies s psi.

Definition globally_logically_equivalent (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi <-> satisfies s psi.

Lemma globally_logically_equivalent_iff phi psi :
  globally_logically_equivalent phi psi
    <->
  global_semantic_consequence phi psi /\ global_semantic_consequence psi phi.
Proof.
  split; [intro Heqv; split | intros [Hcns Hcns']]; intro; [by apply Heqv..| split].
  - by apply Hcns.
  - by apply Hcns'.
Qed.

#[export] Instance global_semantic_consequence_satisfies s :
  Proper (global_semantic_consequence ==> Basics.impl) (satisfies s).
Proof. by intros phi psi Hcns Hphi; apply Hcns, Hphi. Qed.

#[export] Instance global_semantic_consequence_valid :
  Proper (global_semantic_consequence ==> Basics.impl) valid.
Proof. intros phi psi Hcns Hphi s; rewrite <- Hcns; apply Hphi. Qed.

#[export] Instance globally_logically_equivalent_satisfies s :
  Proper (globally_logically_equivalent ==> iff) (satisfies s).
Proof.
  intros phi psi; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

#[export] Instance globally_logically_equivalent_valid :
  Proper (globally_logically_equivalent ==> iff) valid.
Proof. by intros phi psi Heqv; unfold valid, Validity.valid; setoid_rewrite Heqv. Qed.

Section sec_set_global_semantic_consequence.

Context
  `{Set_ Pattern PatternSet}.

Definition set_global_semantic_consequence (Gamma : PatternSet) (phi : Pattern) :=
  forall s, set_satisfies s Gamma -> satisfies s phi.

#[export] Instance set_global_semantic_consequence_proper :
  Proper ((≡) ==> (=) ==> (iff)) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Heqv _phi phi ->.
  by unfold set_global_semantic_consequence; setoid_rewrite Heqv.
Qed.

#[export] Instance set_global_semantic_consequence_proper_subseteq :
  Proper ((⊆) ==> (=) --> Basics.impl) set_global_semantic_consequence.
Proof.
  intros Gamma Gamma' Hsub _phi phi -> HGamma' s HGamma.
  by apply HGamma'; rewrite Hsub.
Qed.

Lemma set_global_semantic_consequence_singleton phi psi :
  set_global_semantic_consequence {[phi]} psi <-> global_semantic_consequence phi psi.
Proof.
  unfold set_global_semantic_consequence, global_semantic_consequence.
  by setoid_rewrite set_satisfies_singleton.
Qed.

Lemma set_global_semantic_consequence_empty_valid phi :
  set_global_semantic_consequence ∅ phi <-> valid phi.
Proof.
  unfold set_global_semantic_consequence, valid.
  apply forall_proper; intro s; split; [| done].
  intro Hempty; apply Hempty; intros e _phi H_phi.
  contradict H_phi; apply not_elem_of_empty.
Qed.

Lemma set_global_semantic_consequence_union_left Gamma Gamma' phi :
  set_global_semantic_consequence Gamma phi ->
  set_global_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_l Gamma Gamma'). Qed.

Lemma set_global_semantic_consequence_union_right Gamma Gamma' phi :
  set_global_semantic_consequence Gamma' phi ->
  set_global_semantic_consequence (Gamma ∪ Gamma') phi.
Proof. by intros HGamma; rewrite <- (union_subseteq_r Gamma Gamma'). Qed.

Lemma valid_set_global_semantic_consequence_any phi Gamma :
  valid phi -> set_global_semantic_consequence Gamma phi.
Proof.
  intro; rewrite <- (empty_subseteq Gamma).
  by apply set_global_semantic_consequence_empty_valid.
Qed.

#[export] Instance global_semantic_consequence_set_consequence Gamma :
  Proper (global_semantic_consequence ==> Basics.impl) (set_global_semantic_consequence Gamma).
Proof. by intros phi psi Hcns Hphi s HGamma; apply Hcns, Hphi. Qed.

#[export] Instance globally_logically_equivalent_set_consequence Gamma :
  Proper (globally_logically_equivalent ==> iff) (set_global_semantic_consequence Gamma).
Proof.
  intros phi psi; rewrite globally_logically_equivalent_iff; intros [Hl Hr].
  by split; [rewrite Hl | rewrite Hr].
Qed.

Lemma set_global_semantic_consequence_and Gamma phi psi :
  set_global_semantic_consequence Gamma (pAnd phi psi)
    <->
  set_global_semantic_consequence Gamma phi /\ set_global_semantic_consequence Gamma psi.
Proof.
  unfold set_global_semantic_consequence.
  setoid_rewrite satisfies_and_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Lemma set_global_semantic_consequence_iff Gamma phi psi :
  set_global_semantic_consequence Gamma (pIff phi psi)
    <->
  set_global_semantic_consequence Gamma (PImpl phi psi)
    /\
  set_global_semantic_consequence Gamma (PImpl psi phi).
Proof.
  unfold set_global_semantic_consequence; setoid_rewrite satisfies_iff_alt_classic.
  by split; [intro Hand; split; intros; apply Hand | intros []; split; itauto].
Qed.

Definition set_global_semantic_consequence_set (Gamma Delta : PatternSet) : Prop :=
  forall (s : Structure), set_satisfies s Gamma -> set_satisfies s Delta.

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
  set_global_semantic_consequence_set Gamma Delta /\ set_global_semantic_consequence_set Delta Gamma .
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
  intros Delta Gamma HDelta phi psi Hphipsi Hphi s HGamma.
  by rewrite <- Hphipsi; apply Hphi; rewrite HDelta.
Qed.

#[export] Instance set_globally_logically_equivalent_set_consequence_proper :
  Proper (set_globally_logically_equivalent_set ==> globally_logically_equivalent ==> iff)
    set_global_semantic_consequence.
Proof.
  intros Gamma Delta Hset_eqv phi psi Heqv; unfold set_global_semantic_consequence.
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

End sec_set_global_semantic_consequence.

End sec_global_semantic_consequence.
