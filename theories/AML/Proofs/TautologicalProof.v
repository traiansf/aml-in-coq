From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.

Section sec_tautology.

Context `{signature}.

Inductive MLPropAxiom : Pattern -> Prop :=
| ax_p1 : forall phi psi,
    MLPropAxiom (PImpl phi (PImpl psi phi))
| ax_p2 : forall phi psi chi,
    MLPropAxiom (PImpl
        (PImpl phi (PImpl psi chi))
        (PImpl (PImpl phi psi) (PImpl phi chi)))
| ax_p3 : forall phi psi,
    MLPropAxiom (PImpl
        (PImpl (pNeg phi) (pNeg psi))
        (PImpl psi phi))
.

Inductive MLModusPonens : Pattern -> Pattern -> Pattern -> Type :=
| rule_modus_ponens : forall phi psi,
    MLModusPonens phi (PImpl phi psi) psi.

Inductive MLTautology : Pattern -> Prop :=
| ml_tauto_ax : forall phi, MLPropAxiom phi -> MLTautology phi
| ml_tauto_modus_ponens : forall phi psi chi,
  MLTautology phi -> MLTautology psi ->
  MLModusPonens phi psi chi ->
  MLTautology psi.

End sec_tautology.
