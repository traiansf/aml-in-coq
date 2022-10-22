From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern.
From AML Require Import Structure Valuation PropositionalPatternValuation.
From AML Require Import Validity.

Section sec_tautology.

Context `{signature}.

Definition Tautology (phi : Pattern) : Prop :=
  forall (s : Structure) F,  PropositionalPatternValuation F -> F phi ≡ top idomain.

Lemma tautology_valid phi : Tautology phi -> valid phi.
Proof. by intros Htauto s e; apply Htauto. Qed.

Lemma tautology_phi_iff_phi phi : Tautology (pIff phi phi).
Proof. by intros s F ?; apply top_pattern_valuation_iff_classic. Qed.

Lemma tautology_phi_or_phi_iff_phi phi : Tautology (pIff (pOr phi phi) phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_iff_phi_and_phi phi : Tautology (pIff phi (pAnd phi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_or_comm phi psi : Tautology (pIff (pOr phi psi) (pOr psi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_and_comm phi psi : Tautology (pIff (pAnd phi psi) (pAnd psi phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_impl_phi_or_psi phi psi : Tautology (PImpl phi (pOr phi psi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_or_classic by done.
  by set_solver.
Qed.

Lemma tautology_phi_and_psi_impl_phi phi psi : Tautology (PImpl (pAnd phi psi) phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, pattern_valuation_and_classic by done.
  by set_solver.
Qed.

Lemma tautology_bot_impl_phi phi : Tautology (PImpl PBot phi).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_impl_classic, ppv_bot by done.
  by set_solver.
Qed.

Lemma tautology_excluded_middle phi : Tautology (pOr phi (pNeg phi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_or_classic, pattern_valuation_neg_classic by done.
  rewrite elem_of_equiv_top; intro a; rewrite elem_of_union, elem_of_complement.
  by apply classic.
Qed.

Lemma tautology_impl_impl_and phi psi chi :
  Tautology (pIff (PImpl phi (PImpl psi chi)) (PImpl (pAnd phi psi) chi)).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic,
    pattern_valuation_and_classic by done.
  rewrite complement_intersection_classic.
  by set_solver.
Qed.

Lemma tautology_impl_impl_comm phi psi chi :
  Tautology (pIff (PImpl phi (PImpl psi chi)) (PImpl psi (PImpl phi chi))).
Proof.
  intros s F ?.
  rewrite top_pattern_valuation_iff_classic, !pattern_valuation_impl_alt_classic
    by done.
  by set_solver.
Qed.

End sec_tautology.
