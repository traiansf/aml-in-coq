From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Structure Satisfaction Validity.
From AML Require Import Valuation PropositionalPatternValuation PatternValuation.
From AML Require Export GlobalSemanticConsequence LocalSemanticConsequence StrongSemanticConsequence.

Section sec_semantic_consequences.

Context `{signature}.

Context
  `{Set_ Pattern PatternSet}.

End sec_semantic_consequences.
