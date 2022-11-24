From stdpp Require Import prelude.
From AML Require Import Signature Pattern Substitution.

Class ReachabilitySignature `{signature} := {next : Sigma}.

Section sec_basic_definitions.

Context `{ReachabilitySignature}.

Definition EX ϕ := PApp (POp next) ϕ.
Definition AX ϕ := ¬ₚ (EX (¬ₚ ϕ)).
Definition can_transition := EX pTop.
Definition is_final := ¬ₚ can_transition.

End sec_basic_definitions.

Declare Scope ml_reach_scope.

Bind Scope ml_reach_scope with ReachabilitySignature.

Notation "∙ x" := (EX x) (at level 41) : ml_reach_scope.
Notation "∘ x" := (AX x) (at level 41) : ml_reach_scope.

Open Scope ml_reach_scope.

Section sec_definitions.

Context `{ReachabilitySignature}.

Definition can_reach_in_one_step (ϕ ψ : Pattern) : Pattern := ϕ →ₚ ∙ ϕ.

Definition AF X ϕ := μₚ X (ϕ ∨ₚ (AX (PSVar X) ∧ₚ can_transition)).
Definition wAF X ϕ := νₚ X (ϕ ∨ₚ (AX (PSVar X) ∧ₚ can_transition)).

Definition EF X ϕ := μₚ X (ϕ ∨ₚ EX (PSVar X)).
Definition wEF X ϕ := νₚ X (ϕ ∨ₚ EX (PSVar X)).

End sec_definitions.

Infix "→ₖ" := can_reach_in_one_step (at level 59, no associativity) : ml_reach_scope.
