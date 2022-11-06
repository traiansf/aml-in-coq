From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import GlobalSemanticConsequence.

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

Lemma local_semantic_consequence_global phi psi :
  local_semantic_consequence phi psi -> global_semantic_consequence phi psi.
Proof. by intros Hlocal s Hphi e; apply Hlocal, Hphi. Qed.

Lemma locally_logically_equivalent_global phi psi :
  locally_logically_equivalent phi psi -> globally_logically_equivalent phi psi.
Proof.
  rewrite locally_logically_equivalent_iff, globally_logically_equivalent_iff.
  by intros []; split; apply local_semantic_consequence_global.
Qed.

Lemma locally_logically_equivalent_evar x y :
  locally_logically_equivalent (PEVar x) (PEVar y).
Proof. by intros s e; rewrite !esatisfies_evar. Qed.

Lemma globally_logically_equivalent_evar x y :
  globally_logically_equivalent (PEVar x) (PEVar y).
Proof.
  by apply locally_logically_equivalent_global, locally_logically_equivalent_evar.
Qed.

Lemma globally_logically_equivalent_not_local :
  exists phi psi, globally_logically_equivalent phi psi /\ ~ local_semantic_consequence phi psi.
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

Lemma set_local_semantic_consequence_global Gamma phi :
  set_local_semantic_consequence Gamma phi -> set_global_semantic_consequence Gamma phi.
Proof. by intros Hlocal s Hphi e; apply Hlocal, Hphi. Qed.

Lemma set_local_semantic_consequence_global_closed_pattern Gamma phi :
  set_closed_pattern Gamma ->
    set_local_semantic_consequence Gamma phi
      <->
    set_global_semantic_consequence Gamma phi.
Proof.
  split; [by apply set_local_semantic_consequence_global |].
  intros Hglobal s e HGamma; apply Hglobal.
  by eapply set_satistifes_closed_pattern; [| eexists].
Qed.

End sec_set_local_semantic_consequence.

End sec_local_semantic_consequence.