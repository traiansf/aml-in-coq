From stdpp Require Import prelude.
From sets Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern PatternTranslation.
From AML.Semantics Require Import Structure Valuation PatternValuation.
From AML.Semantics Require Import Satisfaction GlobalSemanticConsequence.

Section sec_structure_reduct.

Context
  `{sign1 : signature EVar SVar Sigma1 EVarSet SVarSet}
  `{EqDecision Sigma2}
  `{sign2 : !signature EVar SVar Sigma2 EVarSet SVarSet}
  (h : Sigma1 -> Sigma2)
  `{!SignatureMorphism sign1 sign2 h}.

Definition structure_reduct (A : Structure (Sigma := Sigma2))
  : Structure (Sigma := Sigma1) :=
{|
  idomain := idomain;
  iapp := iapp;
  isigma := isigma ∘ h
|}.

Definition valuation_reduct (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := A))
  : Valuation (s := structure_reduct A).
Proof.
  split.
  - exact (eval va).
  - exact (sval va).
Defined.

Definition valuation_reduct_rev (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := structure_reduct A))
  : Valuation (s := A).
Proof.
  split.
  - exact (eval va).
  - exact (sval va).
Defined.

Lemma valuation_reduct_inv_1 (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := A))
  : valuation_reduct_rev A (valuation_reduct A va) ≡ va.
Proof. done. Qed.

Lemma valuation_reduct_inv_2 (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := structure_reduct A))
  : valuation_reduct A (valuation_reduct_rev A va) ≡ va.
Proof. done. Qed.

Lemma valuation_reduct_eupdate A v x vx :
  valuation_reduct A (valuation_eupdate v x vx)
    ≡
  valuation_eupdate (valuation_reduct A v) x vx.
Proof. done. Qed.

Lemma pattern_valuation_reduct
  (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := A))
  (ϕ : Pattern (Sigma := Sigma1))
  : pattern_valuation A va (pattern_translation h ϕ)
    ≡
    pattern_valuation (structure_reduct A) (valuation_reduct A va) ϕ.
Proof.
  revert va; induction ϕ.
  - done.
  - done.
  - by intros; cbn; rewrite IHϕ1, IHϕ2.
  - cbn; intros va a.
    rewrite !elem_of_indexed_union.
    apply exist_proper; intro b.
    by rewrite IHϕ.
  - cbn; intros va a.
    rewrite !elem_of_filtered_intersection.
    apply forall_proper; intros B.
    by rewrite IHϕ.
  - by intro va; cbn; rewrite IHϕ1, IHϕ2.
  - done.
Qed.

Lemma esatisfies_reduct
  (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := A))
  (ϕ : Pattern (Sigma := Sigma1))
  : esatisfies A va (pattern_translation h ϕ)
    <->
    esatisfies (structure_reduct A) (valuation_reduct A va) ϕ.
Proof.
  by unfold esatisfies; rewrite pattern_valuation_reduct.
Qed.

Lemma satisfies_reduct
  (A : Structure (Sigma := Sigma2))
  (ϕ : Pattern (Sigma := Sigma1))
  : satisfies A (pattern_translation h ϕ)
    <->
    satisfies (structure_reduct A) ϕ.
Proof.
  split; [| by intros Hsat va; apply esatisfies_reduct, Hsat].
  intros Hsat va'.
  unfold esatisfies.
  transitivity
    (pattern_valuation A (valuation_reduct_rev A va') (pattern_translation h ϕ));
    [| by apply Hsat].
  rewrite pattern_valuation_reduct.
  apply pattern_valuation_proper; [| done].
  symmetry; apply valuation_reduct_inv_2.
Qed.

Section sec_sets_of_sentences.

Context
  `{FinSet (Pattern (Sigma := Sigma1)) PatternSet1}
  `{FinSet (Pattern (Sigma := Sigma2)) PatternSet2}
  (Γ : PatternSet1).

Lemma set_esatisfies_reduct
  (A : Structure (Sigma := Sigma2))
  (va : Valuation (s := A))
  : set_esatisfies A va (pattern_set_translation h Γ (PatternSet2 := PatternSet2))
    <->
    set_esatisfies (structure_reduct A) (valuation_reduct A va) Γ.
Proof.
  split; intros Hsat.
  - intros ϕ Hϕ; apply esatisfies_reduct, Hsat, elem_of_map.
    by eexists.
  - intros ϕ'.
    unfold pattern_set_translation; rewrite elem_of_map.
    intros (ϕ & -> & Hϕ).
    by apply esatisfies_reduct, Hsat.
Qed.

Lemma set_satisfies_reduct
  (A : Structure (Sigma := Sigma2))
  : set_satisfies A (pattern_set_translation h Γ (PatternSet2 := PatternSet2))
    <->
    set_satisfies (structure_reduct A) Γ.
Proof.
  rewrite !set_satisfies_alt by typeclasses eauto.
  split; intros Hsat.
  - intros ϕ Hϕ; apply satisfies_reduct, Hsat, elem_of_map.
    by eexists.
  - intros ϕ'.
    unfold pattern_set_translation; rewrite elem_of_map.
    intros (ϕ & -> & Hϕ).
    by apply satisfies_reduct, Hsat.
Qed.

Lemma global_semantic_consequence_set_reduct
  (ϕ : Pattern (Sigma := Sigma1))
  : Γ ⊧ ϕ ->
    pattern_set_translation h Γ (PatternSet2 := PatternSet2) ⊧ pattern_translation h ϕ.
Proof.
  intros Hsat M HΓ.
  by apply satisfies_reduct, Hsat, set_satisfies_reduct.
Qed.

End sec_sets_of_sentences.

End sec_structure_reduct.
