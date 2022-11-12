From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Tautology.
From AML Require Import StrongSemanticConsequence LocalSemanticConsequence.

Section sec_global_semantic_consequence.

  Context `{signature}.

Definition global_semantic_consequence (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi -> satisfies s psi.

#[export] Instance global_semantic_consequence_refl : Reflexive global_semantic_consequence.
Proof. by intros ? ?. Qed.

#[export] Instance global_semantic_consequence_trans : Transitive global_semantic_consequence.
Proof.
  intros phi psi chi Hpsi Hchi s Hphi.
  by apply Hchi, Hpsi.
Qed.

Definition globally_logically_equivalent (phi psi : Pattern) : Prop :=
  forall (s : Structure), satisfies s phi <-> satisfies s psi.

#[export] Instance globally_logically_equivalent_refl : Reflexive globally_logically_equivalent.
Proof. by intros ? ?. Qed.

#[export] Instance globally_logically_equivalent_trans : Transitive globally_logically_equivalent.
Proof.
  intros phi psi chi Hpsi Hchi s.
  by etransitivity; [apply Hpsi | apply Hchi].
Qed.

#[export] Instance globally_logically_equivalent_sym : Symmetric globally_logically_equivalent.
Proof.
  intros phi psi Hpsi s.
  by symmetry.
Qed.

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

Lemma local_semantic_consequence_global phi psi :
  local_semantic_consequence phi psi -> global_semantic_consequence phi psi.
Proof. by intros Hlocal s Hphi e; apply Hlocal, Hphi. Qed.

Lemma locally_logically_equivalent_global phi psi :
  locally_logically_equivalent phi psi -> globally_logically_equivalent phi psi.
Proof.
  rewrite locally_logically_equivalent_iff, globally_logically_equivalent_iff.
  by intros []; split; apply local_semantic_consequence_global.
Qed.

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

Section sec_rules.

Lemma set_global_mp Gamma phi psi :
  set_global_semantic_consequence Gamma phi ->
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma psi.
Proof.
  intros Hphi Hphipsi A HGamma e.
  specialize (Hphi A HGamma e).
  specialize (Hphipsi A HGamma e).
  by eapply esatisfies_mp_classic.
Qed.

Lemma set_global_impl_trans Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma (PImpl psi chi) ->
  set_global_semantic_consequence Gamma (PImpl psi chi).
Proof.
  intros Hphipsi Hpsichi A HGamma e.
  specialize (Hphipsi A HGamma e).
  specialize (Hpsichi A HGamma e).
  rewrite esatisfies_impl_classic in Hphipsi, Hpsichi |- *.
  by etransitivity.
Qed.

Lemma set_global_and_curry Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl (pAnd phi psi) chi)
    <->
  set_global_semantic_consequence Gamma (PImpl phi (PImpl psi chi)).
Proof.
  pose proof (Hcurry := tautology_impl_impl_and phi psi chi).
  apply tautology_valid, strongly_logically_equivalent_valid,
    strongly_logically_equivalent_locally, locally_logically_equivalent_global in Hcurry.
  by rewrite Hcurry.
Qed.

Lemma set_global_impl_ex_elim Gamma phi psi x :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  x ∉ FEV psi ->
  set_global_semantic_consequence Gamma (PImpl (PEx x phi) psi).
Proof.
  intros Hphipsi Hx A HGamma e.
  specialize (Hphipsi A HGamma).
  apply esatisfies_impl_classic; cbn.
  unfold satisfies in Hphipsi; setoid_rewrite esatisfies_impl_classic in Hphipsi.
  intro a; rewrite elem_of_indexed_union.
  intros [xa Hxa].
  apply Hphipsi in Hxa.
  cut (pattern_valuation A (valuation_eupdate e x xa) psi ≡ pattern_valuation A e psi);
    [by set_solver |].
  apply pattern_valuation_fv.
  split; [| done].
  rewrite <- EVarFree_FEV in Hx.
  intros x' Hx'; cbn.
  by unfold fn_update; case_decide; [subst |].
Qed.

End sec_rules.

Section sec_application.

Lemma global_semantic_consequence_impl_app_r phi psi chi :
  global_semantic_consequence (PImpl phi psi) (PImpl (PApp chi phi) (PApp chi psi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_impl_app_l phi psi chi :
  global_semantic_consequence (PImpl phi psi) (PImpl (PApp phi chi) (PApp psi chi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_iff_app_r phi psi chi :
  global_semantic_consequence (pIff phi psi) (pIff (PApp chi phi) (PApp chi psi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_iff_app_l phi psi chi :
  global_semantic_consequence (pIff phi psi) (pIff (PApp phi chi) (PApp psi chi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; cbn.
  by intros Hincl e; rewrite Hincl.
Qed.

Lemma global_semantic_consequence_impl_neg phi psi :
  global_semantic_consequence (PImpl phi psi) (PImpl (pNeg psi) (pNeg phi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_impl_classic; setoid_rewrite pattern_valuation_neg_classic;
    [| typeclasses eauto..].
  by intros Hincl e; apply complement_subseteq_proper, Hincl.
Qed.

Lemma global_semantic_consequence_iff_neg phi psi :
  global_semantic_consequence (pIff phi psi) (pIff (pNeg phi) (pNeg psi)).
Proof.
  intros A; unfold satisfies; setoid_rewrite esatisfies_iff_classic; setoid_rewrite pattern_valuation_neg_classic;
    [| typeclasses eauto..].
  by intros Hincl e; apply complement_equiv_proper, Hincl.
Qed.

Lemma global_semantic_consequence_impl_app_neg_l phi psi chi :
  global_semantic_consequence (PImpl phi psi) (PImpl (PApp (pNeg psi) chi) (PApp (pNeg phi) chi)).
Proof.
  etransitivity; [by apply global_semantic_consequence_impl_neg |].
  apply global_semantic_consequence_impl_app_l.
Qed.

Lemma global_semantic_consequence_impl_app_neg_r phi psi chi :
  global_semantic_consequence (PImpl phi psi) (PImpl (PApp chi (pNeg psi)) (PApp chi (pNeg phi))).
Proof.
  etransitivity; [by apply global_semantic_consequence_impl_neg |].
  apply global_semantic_consequence_impl_app_r.
Qed.

Lemma global_semantic_consequence_iff_app_neg_l phi psi chi :
  global_semantic_consequence (pIff phi psi) (pIff (PApp (pNeg phi) chi) (PApp (pNeg psi) chi)).
Proof.
  etransitivity; [by apply global_semantic_consequence_iff_neg |].
  apply global_semantic_consequence_iff_app_l.
Qed.

Lemma global_semantic_consequence_iff_app_neg_r phi psi chi :
  global_semantic_consequence (pIff phi psi) (pIff (PApp chi (pNeg phi)) (PApp chi (pNeg psi))).
Proof.
  etransitivity; [by apply global_semantic_consequence_iff_neg |].
  apply global_semantic_consequence_iff_app_r.
Qed.

Lemma set_global_semantic_consequence_impl_app_elim_l Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma (PImpl (PApp phi chi) (PApp psi chi)).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_elim_r Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma (PImpl (PApp chi phi) (PApp chi psi)).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_elim_r Gamma phi psi chi :
  set_global_semantic_consequence Gamma (pIff phi psi) ->
  set_global_semantic_consequence Gamma (pIff (PApp chi phi) (PApp chi psi)).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_elim_l Gamma phi psi chi :
  set_global_semantic_consequence Gamma (pIff phi psi) ->
  set_global_semantic_consequence Gamma (pIff (PApp phi chi) (PApp psi chi)).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_neg_elim_l Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma (PImpl (PApp (pNeg psi) chi) (PApp (pNeg phi) chi)).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_neg_l.
Qed.

Lemma set_global_semantic_consequence_impl_app_neg_elim_r Gamma phi psi chi :
  set_global_semantic_consequence Gamma (PImpl phi psi) ->
  set_global_semantic_consequence Gamma (PImpl (PApp chi (pNeg psi)) (PApp chi (pNeg phi))).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_impl_app_neg_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_neg_elim_r Gamma phi psi chi :
  set_global_semantic_consequence Gamma (pIff phi psi) ->
  set_global_semantic_consequence Gamma (pIff (PApp chi (pNeg phi)) (PApp chi (pNeg psi))).
Proof.
  apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_iff_app_neg_r.
Qed.

Lemma set_global_semantic_consequence_iff_app_neg_elim_l Gamma phi psi chi :
  set_global_semantic_consequence Gamma (pIff phi psi) ->
  set_global_semantic_consequence Gamma (pIff (PApp (pNeg phi) chi) (PApp (pNeg psi) chi)).
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

Lemma valid_iff_context_or c phi psi:
  csubst c (pOr phi psi) `valid_iff` pOr (csubst c phi) (csubst c psi).
Proof.
  induction c; cbn; [done |..].
  - etransitivity; [| apply valid_iff_app_or_l].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_l.
  - etransitivity; [| apply valid_iff_app_or_r].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_iff_app_r.
Qed.

Lemma valid_iff_context_ex c x phi :
  ~ x ∈ CFEV c ->
  csubst c (PEx x phi) `valid_iff` PEx x (csubst c phi).
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

Lemma valid_impl_context_and c phi psi:
  csubst c (pAnd phi psi) `valid_impl` pAnd (csubst c phi) (csubst c psi).
Proof.
  induction c; cbn; [done |..].
  - etransitivity; [| apply valid_impl_app_and_l].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_impl_app_l.
  - etransitivity; [| apply valid_impl_app_and_r].
    eapply global_semantic_consequence_valid; [| done].
    by apply global_semantic_consequence_impl_app_r.
Qed.

Lemma valid_impl_context_all c x phi :
  ~ x ∈ CFEV c ->
  csubst c (pAll x phi) `valid_impl` pAll x (csubst c phi).
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

Lemma pattern_valuation_context_empty A e c phi :
  pattern_valuation A e phi ≡ ∅ ->
  pattern_valuation A e (csubst c phi) ≡ ∅.
Proof.
  intros Hphi.
  assert (Hphi' : esatisfies A e (pIff phi pBot)).
  {
    apply esatisfies_iff_classic.
    by rewrite Hphi, pattern_valuation_bot.
  }
  apply local_semantic_consequence_context_iff with (c := c),
    esatisfies_iff_classic in Hphi'.
  rewrite Hphi'.
  transitivity (pattern_valuation A e pBot);
    [| by apply pattern_valuation_bot].
  by apply esatisfies_iff_classic, valid_iff_context_bot.
Qed.

Lemma singleton_valiable_rule c1 c2 x phi :
  valid (pNeg (pAnd (csubst c1 (pAnd (PEVar x) phi))
    (csubst c2 (pAnd (PEVar x) (pNeg phi))))).
Proof.
  intros A e.
  apply top_pattern_valuation_neg_classic; [typeclasses eauto |].
  rewrite pattern_valuation_and_classic by typeclasses eauto.
  destruct (classic (eval e x ∈ pattern_valuation A e phi)).
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

Lemma global_semantic_consequence_svar_sub0 phi psi X :
  SFreeFor X psi phi ->
  global_semantic_consequence phi (svar_sub0 X psi phi).
Proof.
  intros Hfree A Hphi e.
  unfold esatisfies; rewrite pattern_valuation_svar_sub0 by done.
  by apply Hphi.
Qed.

Lemma set_global_semantic_consequence_svar_sub0 Gamma phi psi X :
  SFreeFor X psi phi ->
  set_global_semantic_consequence Gamma phi ->
  set_global_semantic_consequence Gamma (svar_sub0 X psi phi).
Proof.
  by intro; apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_svar_sub0.
Qed.

Lemma global_semantic_consequence_ssubst phi psi X :
  global_semantic_consequence phi (ssubst phi X psi).
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
      destruct (classic (y ∈ (BEV phi ∩ EV psi))) as [HOcc | Hnocc].
      * apply evar_rename_iter_fresh_not_bound_to_rename; [by set_solver | done].
      * rewrite elem_of_intersection in Hnocc.
        apply not_and_or in Hnocc as [Hnocc | Hnocc];
          [| contradict Hnocc; apply elem_of_union; left; done].
        by apply evar_rename_iter_fresh_not_bound_to_avoid; set_solver.
    + intro y; rewrite SVarFree_FSV, SVarBound_BSV; intros Hy Hny.
      subst.
      destruct (classic (y ∈ (BSV phi ∩ SV psi))) as [HOcc | Hnocc];
        [by apply svar_rename_iter_fresh_not_bound_to_rename; set_solver |].
      apply svar_rename_iter_fresh_not_bound_to_avoid; [| by set_solver].
      by rewrite evar_rename_iter_BSV; set_solver.
Qed.

Lemma set_global_semantic_consequence_ssubst Gamma phi psi X :
  set_global_semantic_consequence Gamma phi ->
  set_global_semantic_consequence Gamma (ssubst phi X psi).
Proof.
  by apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_ssubst.
Qed.

End sec_set_variables.

Section sec_mu.

Lemma global_semantic_consequence_knaster_tarski phi psi X :
  SFreeFor X psi phi ->
  global_semantic_consequence
    (PImpl (svar_sub0 X psi phi) psi)
    (PImpl (PMu X phi) psi).
Proof.
  intro.
  by apply local_semantic_consequence_global,
    local_semantic_consequence_knaster_tarski.
Qed.

Lemma set_global_semantic_consequence_knaster_tarski Gamma phi psi X :
  SFreeFor X psi phi ->
  set_global_semantic_consequence Gamma (PImpl (svar_sub0 X psi phi) psi) ->
  set_global_semantic_consequence Gamma (PImpl (PMu X phi) psi).
Proof.
  intro.
  by apply global_semantic_consequence_set_consequence,
    global_semantic_consequence_knaster_tarski.
Qed.

End sec_mu.

End sec_set_global_semantic_consequence.

End sec_global_semantic_consequence.
