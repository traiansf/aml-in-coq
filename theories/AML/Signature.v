From stdpp Require Import prelude.

Class signature (EVar SVar Sigma EVarSet SVarSet: Type)
  `{Infinite EVar} `{FinSet EVar EVarSet}
  `{Infinite SVar} `{FinSet SVar SVarSet}
  `{EqDecision Sigma}.

Class SignatureMorphism
  `(sign1 : signature EVar SVar Sigma1 EVarSet SVarSet)
  `{EqDecision Sigma2}
  `(sign2 : !signature EVar SVar Sigma2 EVarSet SVarSet)
  (sm_sigma : Sigma1 -> Sigma2).

Definition extended_signature `(sign1 : signature EVar SVar Sigma EVarSet SVarSet)
  (extra_ops : Type) `{EqDecision extra_ops} :
  signature EVar SVar (Sigma + extra_ops) EVarSet SVarSet.
Proof. done. Defined.

Definition signature_extension `(sign1 : signature EVar SVar Sigma EVarSet SVarSet)
  (extra_ops : Type) `{EqDecision extra_ops}
  : SignatureMorphism sign1 (extended_signature sign1 extra_ops) inl.
Proof. done. Qed.

#[export] Instance EVarInhabited `{signature} : Inhabited EVar := populate (fresh []).

#[export] Instance SVarInhabited `{signature} : Inhabited SVar := populate (fresh []).
