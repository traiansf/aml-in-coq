From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern Structure Variables.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.


Section sec_satisfaction.

Context
  `{signature}
  (s : Structure)
  .


Definition esatisfies e ϕ := pattern_valuation s e ϕ ≡ top idomain.

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

Lemma esatisfies_bot e : ~ esatisfies e pBot.
Proof.
  intros contra. destruct (contra inhabitant) as [_ contra'].
  rewrite pattern_valuation_bot in contra'.
  by apply contra'.
Qed.

Lemma esatisfies_top e : esatisfies e pTop.
Proof. by apply pattern_valuation_top; typeclasses eauto. Qed.

Lemma esatisfies_neg_classic e ϕ : esatisfies e (pNeg ϕ) <-> pattern_valuation s e ϕ ≡ ∅.
Proof. by apply top_pattern_valuation_neg_classic; typeclasses eauto. Qed.

Lemma esatisfies_app e ϕ ψ :
  esatisfies e (PApp ϕ ψ)
    <->
  ext_iapp s (pattern_valuation s e ϕ) (pattern_valuation s e ψ) ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_and_classic e ϕ ψ :
  esatisfies e (pAnd ϕ ψ) <-> esatisfies e ϕ /\ esatisfies e ψ.
Proof. by apply top_pattern_valuation_and_classic; typeclasses eauto. Qed.

Lemma esatisfies_or_classic e ϕ ψ :
  esatisfies e (pOr ϕ ψ)
    <->
  pattern_valuation s e ϕ ∪ pattern_valuation s e ψ ≡ top idomain.
Proof. by apply top_pattern_valuation_or_classic; typeclasses eauto. Qed.

Lemma esatisfies_impl_classic e ϕ ψ :
  esatisfies e (PImpl ϕ ψ)
    <->
  pattern_valuation s e ϕ ⊆ pattern_valuation s e ψ.
Proof. by apply top_pattern_valuation_impl_classic; typeclasses eauto. Qed.

Lemma esatisfies_iff_classic e ϕ ψ :
  esatisfies e (pIff ϕ ψ)
    <->
  pattern_valuation s e ϕ ≡ pattern_valuation s e ψ.
Proof. by apply top_pattern_valuation_iff_classic; typeclasses eauto. Qed.

Lemma esatisfies_iff_alt_classic e ϕ ψ :
  esatisfies e (pIff ϕ ψ)
    <->
  esatisfies e (PImpl ϕ ψ) /\ esatisfies e (PImpl ψ ϕ).
Proof. by apply esatisfies_and_classic. Qed.

Lemma esatisfies_ex e x ϕ :
  esatisfies e (PEx x ϕ)
    <->
  indexed_union (fun a => pattern_valuation s (valuation_eupdate e x a) ϕ) ≡ top idomain.
Proof. done. Qed.

Lemma esatisfies_ex_elim e x ϕ :
  (exists a, esatisfies (valuation_eupdate e x a) ϕ) -> esatisfies e (PEx x ϕ).
Proof.
  rewrite esatisfies_ex.
  intros [a Ha]; rewrite elem_of_equiv_top; intro b.
  rewrite elem_of_indexed_union.
  by exists a; apply Ha.
Qed.

Lemma esatisfies_all_classic e x ϕ :
  esatisfies e (pAll x ϕ)
    <->
  forall a, esatisfies (valuation_eupdate e x a) ϕ.
Proof.
  unfold pAll; rewrite esatisfies_neg_classic, pattern_valuation_ex.
  rewrite empty_indexed_union.
  apply forall_proper; intro a.
  by rewrite pattern_valuation_neg_classic, complement_empty_classic by typeclasses eauto.
Qed.

Lemma esatisfies_mu_elim e X ϕ :
  (forall B, esatisfies (valuation_supdate e X B) ϕ) -> esatisfies e (μₚ X ϕ).
Proof.
  unfold esatisfies; cbn; setoid_rewrite elem_of_equiv_top.
  intros Hall a; apply elem_of_filtered_intersection; intros B HB.
  by apply HB, Hall.
Qed.

Lemma esatisfies_finite_conjunction_classic e ϕs :
  esatisfies e (finite_conjunction ϕs) <-> Forall (esatisfies e) ϕs.
Proof. by apply top_pattern_valuation_finite_conjunction_classic; typeclasses eauto. Qed.

Lemma esatisfies_finite_disjunction_classic e ϕs :
  esatisfies e (finite_disjunction ϕs)
    <->
  ⋃ (map (pattern_valuation s e) ϕs) ≡ top idomain.
Proof.
  by unfold esatisfies; rewrite pattern_valuation_finite_disjunction_classic by typeclasses eauto.
Qed.

Lemma esatisfies_mp_classic e ϕ ψ :
  esatisfies e (PImpl ϕ ψ) -> esatisfies e ϕ -> esatisfies e ψ.
Proof.
  rewrite esatisfies_impl_classic.
  unfold esatisfies; setoid_rewrite elem_of_equiv_top.
  by intros Hsub Hϕ a; apply Hsub, Hϕ.
Qed.

Definition satisfies ϕ : Prop := forall e, esatisfies e ϕ.

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

Lemma satisfies_bot : ~ satisfies pBot.
Proof.
  by intros He; apply esatisfies_bot with inhabitant, He.
Qed.

Lemma satisfies_top : satisfies pTop.
Proof.
  by intro; apply esatisfies_top.
Qed.

Lemma satisfies_and_classic ϕ ψ :
  satisfies (pAnd ϕ ψ) <-> satisfies ϕ /\ satisfies ψ.
Proof.
  by unfold satisfies; setoid_rewrite esatisfies_and_classic; firstorder.
Qed.

Lemma satisfies_mp_classic ϕ ψ :
  satisfies (PImpl ϕ ψ) -> satisfies ϕ -> satisfies ψ.
Proof.
  intros Hϕψ Hϕ e.
  eapply esatisfies_mp_classic; [apply Hϕψ | apply Hϕ].
Qed.

Lemma satisfies_iff_alt_classic ϕ ψ :
  satisfies (pIff ϕ ψ)
    <->
  satisfies (PImpl ϕ ψ) /\ satisfies (PImpl ψ ϕ).
Proof.
  unfold satisfies; setoid_rewrite esatisfies_iff_alt_classic.
  by split; [| itauto]; intros He; split; intro; apply He.
Qed.

Lemma satisfies_all_classic x ϕ :
  satisfies (pAll x ϕ) <-> satisfies ϕ.
Proof.
  split; intros Hsat e; cycle 1.
  - by apply esatisfies_all_classic; intro; apply Hsat.
  - specialize (Hsat e); rewrite esatisfies_all_classic in Hsat.
    specialize (Hsat (eval e x)).
    by rewrite valuation_eupdate_id in Hsat.
Qed.

Lemma satisfies_finite_conjunction_classic ϕs :
  satisfies (finite_conjunction ϕs) <-> Forall satisfies ϕs.
Proof.
  unfold satisfies; setoid_rewrite esatisfies_finite_conjunction_classic.
  setoid_rewrite Forall_forall.
  itauto.
Qed.

Context `{Set_ Pattern PatternSet}.

Definition set_esatisfies (e : Valuation) (Gamma : PatternSet) :=
  forall ϕ, ϕ ∈ Gamma -> esatisfies e ϕ.

#[export] Instance set_esatisfies_proper (e : Valuation) :
  Proper ((≡) ==> (iff)) (set_esatisfies e).
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall ϕ Hϕ; apply Hall, Heqv.
Qed.

#[export] Instance set_esatisfies_proper_subseteq (e : Valuation) :
  Proper ((⊆) --> Basics.impl) (set_esatisfies e).
Proof. by intros Gamma Gamma' Heqv Hall ϕ Hϕ; apply Hall, Heqv. Qed.

Lemma set_esatisfies_singleton e ϕ :
  set_esatisfies e {[ϕ]} <-> esatisfies e ϕ.
Proof.
  unfold set_esatisfies; setoid_rewrite elem_of_singleton.
  by split; [intros Hsat| intros Hsat _ϕ ->]; apply Hsat.
Qed.

Definition set_satisfies (Gamma : PatternSet) :=
  forall e, set_esatisfies e Gamma.

Lemma set_satisfies_alt Gamma :
  set_satisfies Gamma <-> forall ϕ, ϕ ∈ Gamma -> satisfies ϕ.
Proof.
  unfold set_satisfies, set_esatisfies, satisfies. 
  by firstorder.
Qed.

#[export] Instance set_satisfies_proper :
  Proper ((≡) ==> (iff)) set_satisfies.
Proof.
  intros Gamma Gamma' Heqv.
  by split; intros Hall e ϕ Hϕ; apply Hall, Heqv.
Qed.

#[export] Instance set_satisfies_proper_subseteq :
  Proper ((⊆) --> Basics.impl) set_satisfies.
Proof. by intros Gamma Gamma' Heqv Hall e ϕ Hϕ; apply Hall, Heqv. Qed.

Lemma set_satisfies_singleton ϕ :
  set_satisfies {[ϕ]} <-> satisfies ϕ.
Proof.
  by unfold set_satisfies; setoid_rewrite set_esatisfies_singleton.
Qed.

Lemma set_esatisfies_set_pattern_valuation e Gamma :
  set_esatisfies e Gamma <-> set_pattern_valuation s e Gamma ≡ top idomain.
Proof. by rewrite top_set_pattern_valuation. Qed.

Lemma esatisfies_closed_pattern e1 e2 ϕ :
  ClosedPattern ϕ -> esatisfies e1 ϕ <-> esatisfies e2 ϕ.
Proof.
  by intros; unfold esatisfies; rewrite pattern_valuation_closed_pattern.
Qed.

Lemma satistifes_closed_pattern ϕ :
  ClosedPattern ϕ -> satisfies ϕ <-> exists e, esatisfies e ϕ.
Proof.
  split; [intros Hsat; exists inhabitant; apply Hsat |].
  by intros [e He] e'; eapply esatisfies_closed_pattern.
Qed.

Lemma set_esatisfies_closed_pattern e1 e2 Gamma :
  set_closed_pattern Gamma -> set_esatisfies e1 Gamma <-> set_esatisfies e2 Gamma.
Proof.
  intro HGamma; apply forall_proper; intro ϕ; unfold esatisfies.
  by split; intros Hsat Hϕ;
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
