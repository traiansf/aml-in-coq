From stdpp Require Import prelude.
From Coq Require Import Classical.
From sets Require Import Ensemble.
From AML Require Import Signature Pattern.
From AML Require Import Structure Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Validity.

Section sec_tautology.

Context `{signature}.

Definition Tautology (ϕ : Pattern) : Prop :=
  forall (s : Structure) F,  PropositionalPatternValuation F -> F ϕ ≡ top idomain.

Lemma tautology_valid ϕ : Tautology ϕ -> valid ϕ.
Proof. intros Htauto s e; apply Htauto; typeclasses eauto. Qed.

Lemma tautology_ϕ_iff_ϕ ϕ : Tautology (pIff ϕ ϕ).
Proof. by intros s F ?; apply top_pattern_valuation_iff_classic. Qed.

Lemma tautology_ϕ_or_ϕ_iff_ϕ ϕ : Tautology (pIff (pOr ϕ ϕ) ϕ).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_ϕ_iff_ϕ_and_ϕ ϕ : Tautology (pIff ϕ (pAnd ϕ ϕ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_or_comm ϕ ψ : Tautology (pIff (pOr ϕ ψ) (pOr ψ ϕ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_and_comm ϕ ψ : Tautology (pIff (pAnd ϕ ψ) (pAnd ψ ϕ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_ϕ_impl_ϕ_or_ψ ϕ ψ : Tautology (PImpl ϕ (pOr ϕ ψ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_ϕ_and_ψ_impl_ϕ ϕ ψ : Tautology (PImpl (pAnd ϕ ψ) ϕ).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_bot_impl_ϕ ϕ : Tautology (PImpl pBot ϕ).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, ppv_bot by done.
  by set_solver.
Qed.

Lemma tautology_excluded_middle ϕ : Tautology (pOr ϕ (pNeg ϕ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_or_classic, pattern_valuation_neg_classic by done.
  rewrite elem_of_equiv_top; intro a; rewrite elem_of_union, elem_of_complement.
  by apply classic.
Qed.

Lemma tautology_impl_impl_and ϕ ψ χ :
  Tautology (pIff (PImpl ϕ (PImpl ψ χ)) (PImpl (pAnd ϕ ψ) χ)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic,
    pattern_valuation_and_classic by done.
  rewrite complement_intersection_classic.
  by set_solver.
Qed.

Lemma tautology_impl_impl_comm ϕ ψ χ :
  Tautology (pIff (PImpl ϕ (PImpl ψ χ)) (PImpl ψ (PImpl ϕ χ))).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic
    by done.
  by set_solver.
Qed.

End sec_tautology.
