From stdpp Require Import prelude.

Class signature : Type := {
    EVar : Type;
    EVar_infinite :> Infinite EVar;
    EVar_dec :> EqDecision EVar;
    SVar : Type;
    SVar_infinite :> Infinite SVar;
    SVar_dec :> EqDecision SVar;
    Sigma : Type;
    Sigma_dec :> EqDecision Sigma;
  }.
  