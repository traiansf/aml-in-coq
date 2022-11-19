From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof.

Section sec_proof_system.

Context `{signature}.

Inductive MLAxiom : Pattern -> Prop :=
| ax_ex_quantifier : forall x y phi,
    MLAxiom (PImpl (evar_sub0 x (PEVar y) phi) (PEx x phi))
| ax_propagation_bot_l : forall phi,
    MLAxiom (PImpl (PApp pBot phi) pBot)
| ax_propagation_bot_r : forall phi,
    MLAxiom (PImpl (PApp phi pBot) pBot)
| ax_propagation_or_l : forall phi psi chi,
    MLAxiom (PImpl (PApp (pOr phi psi) chi) (pOr (PApp phi chi) (PApp psi chi)))
| ax_propagation_or_r : forall phi psi chi,
    MLAxiom (PImpl (PApp chi (pOr phi psi)) (pOr (PApp chi phi) (PApp chi psi)))
| ax_propagation_ex_l : forall x phi psi,
    x ∉ FEV psi ->
    MLAxiom (PImpl (PApp (PEx x phi) psi) (PEx x (PApp phi psi)))
| ax_propagation_ex_r : forall x phi psi,
    x ∉ FEV psi ->
    MLAxiom (PImpl (PApp psi (PEx x phi)) (PEx x (PApp psi phi)))
| ax_pre_fixpoint : forall X phi,
    OccursPositively X phi ->
    SFreeFor X (PMu X phi) phi ->
    MLAxiom (PImpl (svar_sub0 X (PMu X phi) phi) (PMu X phi))
| ax_existence : forall x,
    MLAxiom (PEx x (PEVar x))
| ax_singleton_variable : forall x phi C1 C2,
    MLAxiom (pNeg (pAnd (csubst C1 (pAnd x phi)) (csubst C2 (pAnd x (pNeg phi)))))
.

Inductive MLSinglePremiseRule : Pattern -> Pattern -> Prop := 
| rule_ex_quantifier : forall x phi psi,
    ~ x ∈ FEV psi ->
    MLSinglePremiseRule (PImpl phi psi) (PImpl (PEx x phi) psi)
| rule_framing_l : forall phi psi chi,
    MLSinglePremiseRule (PImpl phi psi) (PImpl (PApp phi chi) (PApp psi chi))
| rule_framing_r : forall phi psi chi,
    MLSinglePremiseRule (PImpl phi psi) (PImpl (PApp chi phi) (PApp chi psi))
| rule_set_variable_substitution : forall phi X psi,
    SFreeFor X psi phi ->
    MLSinglePremiseRule phi (svar_sub0 X psi phi)
| rule_knaster_tarsky : forall phi X psi,
    SFreeFor X psi phi ->
    MLSinglePremiseRule (PImpl (svar_sub0 X psi phi) psi) (PImpl (PMu X phi) psi)
.

End sec_proof_system.
