From AML Require Import Ensemble Signature.
From stdpp Require Import prelude.

Class Structure `{signature} : Type :=
{
  idomain : Type;
  non_empty :> Inhabited idomain;
  iapp : idomain -> idomain -> Ensemble idomain;
  isigma : Sigma -> Ensemble idomain
}.
