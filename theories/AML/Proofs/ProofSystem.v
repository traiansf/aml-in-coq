From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof.

Section sec_proof_system.

Context `{signature}.

Inductive MLAxiom : Pattern -> Prop :=
| ax_ex_quantifier : forall x y ϕ,
    MLAxiom (PImpl (evar_sub0 x (PEVar y) ϕ) (PEx x ϕ))
| ax_propagation_bot_l : forall ϕ,
    MLAxiom (PImpl (PApp pBot ϕ) pBot)
| ax_propagation_bot_r : forall ϕ,
    MLAxiom (PImpl (PApp ϕ pBot) pBot)
| ax_propagation_or_l : forall ϕ ψ χ,
    MLAxiom (PImpl (PApp (pOr ϕ ψ) χ) (pOr (PApp ϕ χ) (PApp ψ χ)))
| ax_propagation_or_r : forall ϕ ψ χ,
    MLAxiom (PImpl (PApp χ (pOr ϕ ψ)) (pOr (PApp χ ϕ) (PApp χ ψ)))
| ax_propagation_ex_l : forall x ϕ ψ,
    x ∉ FEV ψ ->
    MLAxiom (PImpl (PApp (PEx x ϕ) ψ) (PEx x (PApp ϕ ψ)))
| ax_propagation_ex_r : forall x ϕ ψ,
    x ∉ FEV ψ ->
    MLAxiom (PImpl (PApp ψ (PEx x ϕ)) (PEx x (PApp ψ ϕ)))
| ax_pre_fixpoint : forall X ϕ,
    OccursPositively X ϕ ->
    SFreeFor X (μₚ X ϕ) ϕ ->
    MLAxiom (PImpl (svar_sub0 X (μₚ X ϕ) ϕ) (μₚ X ϕ))
| ax_existence : forall x,
    MLAxiom (PEx x (PEVar x))
| ax_singleton_variable : forall x ϕ C1 C2,
    MLAxiom (pNeg (pAnd (csubst C1 (pAnd x ϕ)) (csubst C2 (pAnd x (pNeg ϕ)))))
.

Inductive MLSinglePremiseRule : Pattern -> Pattern -> Prop := 
| rule_ex_quantifier : forall x ϕ ψ,
    ~ x ∈ FEV ψ ->
    MLSinglePremiseRule (PImpl ϕ ψ) (PImpl (PEx x ϕ) ψ)
| rule_framing_l : forall ϕ ψ χ,
    MLSinglePremiseRule (PImpl ϕ ψ) (PImpl (PApp ϕ χ) (PApp ψ χ))
| rule_framing_r : forall ϕ ψ χ,
    MLSinglePremiseRule (PImpl ϕ ψ) (PImpl (PApp χ ϕ) (PApp χ ψ))
| rule_set_variable_substitution : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    MLSinglePremiseRule ϕ (svar_sub0 X ψ ϕ)
| rule_knaster_tarsky : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    MLSinglePremiseRule (PImpl (svar_sub0 X ψ ϕ) ψ) (PImpl (μₚ X ϕ) ψ)
.

End sec_proof_system.
