From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern Substitution Reachability.
From AML.Semantics Require Import Structure Valuation PatternValuation.

Section sec_transition_system.

Print pattern_valuation.

Context
  `{ReachabilitySignature}
  (s : Structure)
  (e : Valuation)
  .

Definition phi_or_next_on_all_paths_fn X ϕ :=
  pattern_valuation_fn s (ϕ ∨ₚ (AX (PSVar X) ∧ₚ can_transition)) X e.
