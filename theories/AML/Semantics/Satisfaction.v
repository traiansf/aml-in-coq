From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern Structure Variables.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.


Section sec_satisfaction.

Context
  [sign : signature]
  (s : Structure)
  .


Definition esatisfies e phi := pattern_valuation s e phi ≡ top idomain.

Lemma esatisfies_evar e x : esatisfies e (PEVar x) <-> exists a, top idomain ≡ {[a]}.
Proof.
  unfold esatisfies; cbn; split; [by eexists |].
  intros [a Ha] _a; split; [done |].
  assert (He : eval e x ∈ top idomain) by done.
  rewrite Ha, !elem_of_singleton in *; congruence.
Qed.

Lemma esatisfies_svar e X : esatisfies e (PSVar X) <-> sval e X ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_cons e op : esatisfies e (POp op) <-> isigma op ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_bot e : ~ esatisfies e (@PBot sign).
Proof.
  intros contra. destruct (contra inhabitant) as [_ contra'].
  by apply contra'.
Qed.

Lemma esatisfies_top e : esatisfies e (@pTop sign).
Proof. by apply pattern_valuation_top. Qed.

Lemma esatisfies_neg_classic e phi : esatisfies e (pNeg phi) <-> pattern_valuation s e phi ≡ ∅.
Proof. by apply top_pattern_valuation_neg_classic. Qed.

Lemma esatisfies_app e phi psi :
  esatisfies e (PApp phi psi)
    <->
  ext_iapp s (pattern_valuation s e phi) (pattern_valuation s e psi) ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_and_classic e phi psi :
  esatisfies e (pAnd phi psi) <-> esatisfies e phi /\ esatisfies e psi.
Proof. by apply top_pattern_valuation_and_classic. Qed.

Lemma esatisfies_or_classic e phi psi :
  esatisfies e (pOr phi psi)
    <->
  pattern_valuation s e phi ∪ pattern_valuation s e psi ≡ top idomain.
Proof. by apply top_pattern_valuation_or_classic. Qed.

Lemma esatisfies_impl_classic e phi psi :
  esatisfies e (PImpl phi psi)
    <->
  pattern_valuation s e phi ⊆ pattern_valuation s e psi.
Proof. by apply top_pattern_valuation_impl_classic. Qed.

Lemma esatisfies_iff_classic e phi psi :
  esatisfies e (pIff phi psi)
    <->
  pattern_valuation s e phi ≡ pattern_valuation s e psi.
Proof. by apply top_pattern_valuation_iff_classic. Qed.

Lemma esatisfies_iff_alt_classic e phi psi :
  esatisfies e (pIff phi psi)
    <->
  esatisfies e (PImpl phi psi) /\ esatisfies e (PImpl psi phi).
Proof. by apply esatisfies_and_classic. Qed.

Lemma esatisfies_ex e x phi :
  esatisfies e (PEx x phi)
    <->
  indexed_union (fun a => pattern_valuation s (valuation_eupdate e x a) phi) ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_ex_elim e x phi :
  (exists a, esatisfies (valuation_eupdate e x a) phi) -> esatisfies e (PEx x phi).
Proof.
  rewrite esatisfies_ex.
  intros [a Ha]; rewrite elem_of_equiv_top; intro b.
  rewrite elem_of_indexed_union.
  by exists a; apply Ha.
Qed.

Lemma esatisfies_all_classic e x phi :
  esatisfies e (pAll x phi)
    <->
  forall a, esatisfies (valuation_eupdate e x a) phi.
Proof.
  unfold pAll; rewrite esatisfies_neg_classic; cbn.
  rewrite empty_indexed_union.
  apply forall_proper; intro a.
  by rewrite complement_empty_classic, difference_empty .
Qed.

Lemma esatisfies_mu_elim e X phi :
  (forall B, esatisfies (valuation_supdate e X B) phi) -> esatisfies e (PMu X phi).
Proof.
  unfold esatisfies; cbn; setoid_rewrite elem_of_equiv_top.
  intros Hall a; apply elem_of_filtered_intersection; intros B HB.
  by apply HB, Hall.
Qed.

Lemma esatisfies_finite_conjunction_classic e phis :
  esatisfies e (finite_conjunction phis) <-> Forall (esatisfies e) phis.
Proof. by apply top_pattern_valuation_finite_conjunction_classic. Qed.

Lemma esatisfies_finite_disjunction_classic e phis :
  esatisfies e (finite_disjunction phis)
    <->
  ⋃ (map (pattern_valuation s e) phis) ≡ top idomain.
Proof.
  by unfold esatisfies; rewrite pattern_valuation_finite_disjunction_classic.
Qed.

Definition satisfies phi : Prop := forall e, esatisfies e phi.

Lemma satisfies_evar x : satisfies (PEVar x) <-> exists a, top idomain ≡ {[a]}.
Proof.
  split; intros He.
  - by eapply esatisfies_evar with (e := inhabitant), He.
  - by intro e; apply esatisfies_evar.
Qed.

Lemma satisfies_cons op : satisfies (POp op) <-> isigma op ≡ top idomain.
Proof.
  split; intros He.
  - by apply He with (e := inhabitant).
  - by intro e; apply esatisfies_cons.
Qed.

Lemma satisfies_bot : ~ satisfies (@PBot sign).
Proof.
  by intros He; apply esatisfies_bot with inhabitant, He.
Qed.

Lemma satisfies_top : satisfies (@pTop sign).
Proof.
  by intro; apply esatisfies_top.
Qed.

Lemma satisfies_and_classic phi psi :
  satisfies (pAnd phi psi) <-> satisfies phi /\ satisfies psi.
Proof.
  by unfold satisfies; setoid_rewrite esatisfies_and_classic; firstorder.
Qed.

Lemma satisfies_mp_classic phi psi :
  satisfies (PImpl phi psi) -> satisfies phi -> satisfies psi.
Proof.
  unfold satisfies; setoid_rewrite esatisfies_impl_classic.
  unfold esatisfies; setoid_rewrite elem_of_equiv_top.
  by intros Hsub Hphi e a; apply Hsub, Hphi.
Qed.

Lemma satisfies_iff_alt_classic phi psi :
  satisfies (pIff phi psi)
    <->
  satisfies (PImpl phi psi) /\ satisfies (PImpl psi phi).
Proof.
  unfold satisfies; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma satisfies_all_classic x phi :
  satisfies (pAll x phi) <-> satisfies phi.
Proof.
  split; intros Hsat e; cycle 1.
  - by apply esatisfies_all_classic; intro; apply Hsat.
  - specialize (Hsat e); rewrite esatisfies_all_classic in Hsat.
    specialize (Hsat (eval e x)).
    by rewrite valuation_eupdate_id in Hsat.
Qed.

Lemma satisfies_finite_conjunction_classic phis :
  satisfies (finite_conjunction phis) <-> Forall satisfies phis.
Proof.
  unfold satisfies; setoid_rewrite esatisfies_finite_conjunction_classic.
  setoid_rewrite Forall_forall.
  itauto.
Qed.

Context `{Set_ (@Pattern sign) PatternSet}.

Definition set_esatisfies (e : Valuation) (Gamma : PatternSet) :=
  forall phi, phi ∈ Gamma -> esatisfies e phi.

#[export] Instance set_esatisfies_proper (e : Valuation) :
  Proper ((≡) ==> (iff)) (set_esatisfies e).
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall phi Hphi; apply Hall, Heqv.
Qed.

#[export] Instance set_esatisfies_proper_subseteq (e : Valuation) :
  Proper ((⊆) --> Basics.impl) (set_esatisfies e).
Proof. by intros Gamma Gamma' Heqv Hall phi Hphi; apply Hall, Heqv. Qed.

Lemma set_esatisfies_singleton e phi :
  set_esatisfies e {[phi]} <-> esatisfies e phi.
Proof.
  unfold set_esatisfies; setoid_rewrite elem_of_singleton.
  by split; [intros Hsat| intros Hsat _phi ->]; apply Hsat.
Qed.

Definition set_satisfies (Gamma : PatternSet) :=
  forall e, set_esatisfies e Gamma.

#[export] Instance set_satisfies_proper :
  Proper ((≡) ==> (iff)) set_satisfies.
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall e phi Hphi; apply Hall, Heqv.
Qed.

#[export] Instance set_satisfies_proper_subseteq :
  Proper ((⊆) --> Basics.impl) set_satisfies.
Proof. by intros Gamma Gamma' Heqv Hall e phi Hphi; apply Hall, Heqv. Qed.

Lemma set_satisfies_singleton phi :
  set_satisfies {[phi]} <-> satisfies phi.
Proof.
  by unfold set_satisfies; setoid_rewrite set_esatisfies_singleton.
Qed.

Lemma set_esatisfies_set_pattern_valuation e Gamma :
  set_esatisfies e Gamma <-> set_pattern_valuation s e Gamma ≡ top idomain.
Proof. by rewrite top_set_pattern_valuation. Qed.

Lemma esatisfies_closed_pattern e1 e2 phi :
  ClosedPattern phi -> esatisfies e1 phi <-> esatisfies e2 phi.
Proof.
  by intros; unfold esatisfies; rewrite pattern_valuation_closed_pattern.
Qed.

Lemma satistifes_closed_pattern phi :
  ClosedPattern phi -> satisfies phi <-> exists e, esatisfies e phi.
Proof.
  split; [intros Hsat; exists inhabitant; apply Hsat |].
  by intros [e He] e'; eapply esatisfies_closed_pattern.
Qed.

Lemma set_esatisfies_closed_pattern e1 e2 Gamma :
  set_closed_pattern Gamma -> set_esatisfies e1 Gamma <-> set_esatisfies e2 Gamma.
Proof.
  intro HGamma; apply forall_proper; intro phi; unfold esatisfies.
  by split; intros Hsat Hphi;
    (rewrite pattern_valuation_closed_pattern; [by apply Hsat |]);
    apply HGamma.
Qed.

Lemma set_satistifes_closed_pattern Gamma :
  set_closed_pattern Gamma -> set_satisfies Gamma <-> exists e, set_esatisfies e Gamma.
Proof.
  split; [intros Hsat; exists inhabitant; apply Hsat |].
  by intros [e He] e'; eapply set_esatisfies_closed_pattern.
Qed.

End sec_satisfaction.
