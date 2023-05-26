From stdpp Require Import prelude.
From sets Require Import Ensemble.
From AML Require Import Signature.

Class Structure `{signature} : Type :=
{
  idomain : Type;
  non_empty :: Inhabited idomain;
  iapp : idomain -> idomain -> Ensemble idomain;
  isigma : Sigma -> Ensemble idomain
}.
