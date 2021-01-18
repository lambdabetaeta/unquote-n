open import Data.Nat

mutual
  data context : Set where
    ∅ : context
    _,_ : Exp → context → context

  data Exp : ℕ → Set where
    var : ℕ → Exp
    app : Exp → Exp → Exp
    lam : Exp → Exp


-- not even going to be structurally recursive:
-- unquote-n : {γ : context} → Exp → Exp
