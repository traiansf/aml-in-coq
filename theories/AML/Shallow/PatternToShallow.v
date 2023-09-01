From Coq Require Import Classical.
From stdpp Require Import prelude.
From sets Require Import Functions Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.
From AML Require Import Shallow.

Section sec_pattern_to_shallow .

Context `{app : Element -> Element -> Ensemble Element} `{!ShallowMLContext app}  `{signature}.

Fixpoint patternToShallow (p : Pattern.Pattern) : @Shallow.Pattern Element.
Proof.
  destruct p.
Abort.

End sec_pattern_to_shallow .
