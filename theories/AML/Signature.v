From stdpp Require Import prelude.

Class signature (EVar SVar Sigma EVarSet SVarSet: Type)
  `{Infinite EVar} `{FinSet EVar EVarSet}
  `{Infinite SVar} `{FinSet SVar SVarSet}
  `{EqDecision Sigma}.

#[export] Instance SVarInhabited `{signature} : Inhabited SVar := populate (fresh []).
