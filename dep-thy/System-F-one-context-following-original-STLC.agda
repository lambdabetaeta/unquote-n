open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (suc ; Fin)
open import Data.Nat using (ℕ; _≟_; suc; zero)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Data.Sum
-- open import Relation.Negation
open import Data.Empty

mutual
  -- NOTE: with self types, everything in context is of same context, rather than
  -- sequentially increasing contexts. This eliminates the need for weakening in
  -- the next constructor of InCtx, which in turn removes the need to prove certian
  -- commutivity lemmas later.

  -- Context = Self(Γ) . List (Σ n (Type n Γ))

  data Context : Set where
    ∅ : Context
    _,_ : ∀{n} → (Γ : Context) → Type n Γ → Context

  data Type : ℕ → Context → Set where
    Π : ∀{n Γ} → (A : Type n Γ) → (Type n (Γ , A)) → Type n Γ
    cumu : ∀{n Γ} → Type n Γ → Type (suc n) Γ
    type : ∀{Γ} → (n : ℕ) → Type (suc n) Γ
    Var : ∀{Γ n} → InCtx Γ (type n) → Type (suc n) Γ
    -- fromE : ∀{Γ n} → Nf Γ (type n) → Type n Γ -- If I ever use this, should be Nf, as even Exps need to use Nf's for types.

  data Pre : Context → Context → Set where
    same : ∀{Γ} → Pre Γ Γ
    next : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₂} → Pre Γ₁ Γ₂ → Pre Γ₁ (Γ₂ , T)

  preCompare : ∀{Γ₁ Γ₂ Γ₃} → (Pre Γ₁ Γ₃) → (Pre Γ₂ Γ₃)
    → (Pre Γ₁ Γ₂ ⊎ Pre Γ₂ Γ₁)
  preCompare same pre₂ = inj₂ pre₂ -- NOTE that there is overlap if both are same.
  preCompare pre₁ same = inj₁ pre₁ -- They actually give the same anwer on overlap.
  preCompare (next pre₁) (next pre₂) = preCompare pre₁ pre₂ -- could resolve with four cases, for all four options.

  --          ↓ ↓    ↓    ↓            ↓   These make the arguments to any weakening function, by specifying how the context is being weakened.
  weakenΓ : ∀{Γ Γpre n} → Pre Γpre Γ → Type n Γpre → Context
  weakenΓ (same {Γ}) T = Γ , T
  weakenΓ (next {_} {_} {_} {T} pre) A = weakenΓ pre A , weakenType pre A T

  weakenType : ∀{Γ Γpre n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → Type m Γ → Type m (weakenΓ pre W)
  weakenType pre W (Π A B) = Π (weakenType pre W A) (weakenType (next pre) W B)
  weakenType pre W (cumu T) = cumu (weakenType pre W T)
  weakenType pre W (type n) = type n
  weakenType pre W (Var x) = Var (weakenICX pre W x)

  -- TASK: define weakenTypeComm.

  weakenPreLeftCtx : ∀{Γ Γpre Γw n} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → Pre Γw Γ → Context
  weakenPreLeftCtx {Γ} {_} {Γw} same W same = Γw
  weakenPreLeftCtx {Γ} {_} {Γw} same W (next prew) = Γw
  weakenPreLeftCtx (next {_} {_} {_} {T} pre) W same = weakenΓ (next {_} {_} {_} {T} pre) W
  weakenPreLeftCtx (next pre) W (next prew) = weakenPreLeftCtx pre W prew

  weakenPreLeftCtxType : ∀{Γ Γpre Γw n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (prew : Pre Γw Γ)
    → Type m Γw → Type m (weakenPreLeftCtx pre W prew)
  weakenPreLeftCtxType same W same T = T
  weakenPreLeftCtxType same W (next prew) T = T
  weakenPreLeftCtxType (next pre) W same T = weakenType (next pre) W T
  weakenPreLeftCtxType (next pre) W (next prew) T = weakenPreLeftCtxType pre W prew T

  weakenPre : ∀{Γ Γpre Γw n} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (prew : Pre Γw Γ)
    → Pre (weakenPreLeftCtx pre W prew) (weakenΓ pre W)
  weakenPre same W same = next same
  weakenPre same W (next prew) = next (next prew)
  weakenPre (next pre) W same = same
  weakenPre (next pre) W (next prew) = next (weakenPre pre W prew)

  for next time:
  -- I think that proving these commutivity properties (or thinking of alternate
  -- contexts which don't require them somehow)
  -- Is the next most useful thing to do, regardless of design.

  weakenCtxComm : ∀{n1 n2 Γ Γ₁ Γ₂}
    → {W₁ : Type n1 Γ₁} → {W₂ : Type n2 Γ₂}
    → (pre₁ : Pre Γ₁ Γ) → (pre₂ : Pre Γ₂ Γ)
    → weakenΓ (weakenPre pre₁ W₁ pre₂) (weakenPreLeftCtxType pre₁ W₁ pre₂ W₂)
      ≡ weakenΓ (weakenPre pre₂ W₂ pre₁) (weakenPreLeftCtxType pre₂ W₂ pre₁ W₁)
  weakenCtxComm same same = {!   !} -- clearly something is defined wrong above, as this is clearly incorrect.
  weakenCtxComm same (next pre₂) = refl
  weakenCtxComm (next pre₁) same = refl
  -- May need a custom dependently typed cong₂
  weakenCtxComm (next pre₁) (next pre₂) = {! cong₂ _,_ (weakenCtxComm pre₁ pre₂) (weakenTypeComm pre₁ pre₂)  !}

  weakenTypeComm : ∀{nA n1 n2 Γ Γ₁ Γ₂} → {A : Type nA Γ}
    → {W₁ : Type n1 Γ₁} → {W₂ : Type n2 Γ₂}
    → (pre₁ : Pre Γ₁ Γ) → (pre₂ : Pre Γ₂ Γ)
    → weakenType (weakenPre pre₁ W₁ pre₂) (weakenPreLeftCtxType pre₁ W₁ pre₂ W₂) (weakenType pre₁ W₁ A)
      ≡ let value = weakenType (weakenPre pre₂ W₂ pre₁) (weakenPreLeftCtxType pre₂ W₂ pre₁ W₁) (weakenType pre₂ W₂ A)
        in subst (λ Γ → Type nA Γ) (weakenCtxComm pre₂ pre₁) value
  weakenTypeComm = {!   !}

  data InCtx : ∀{n} → (Γ : Context) → Type n Γ → Set where
    same : ∀{Γ n T} → InCtx {n} (Γ , T) (weakenType same T T)
    next : ∀{Γ n m A} → {T : Type m Γ} → InCtx {n} Γ A → InCtx (Γ , T) (weakenType same T A)
    --  NOTE: in the above line, this is why "one context" design is hard. Need to weaken in InCtx, makes
    -- weakenICX very hard.

  weakenICX : ∀{Γ Γpre n m T} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → InCtx {m} Γ T → InCtx {m} (weakenΓ pre W) (weakenType pre W T)
  weakenICX same W x = next x
  weakenICX {Γ} {_} {_} {_} {T} (next pre) W (same {_} {_} {T₁})
    = {! InCtx.same {weakenΓ pre W} {_} {weakenType pre W T₁}  !}
    -- = {! subst (λ A → InCtx (weakenΓ pre W , weakenType pre W T₁) A) ? (InCtx.same {weakenΓ pre W} {_} {weakenType pre W T₁})  !}
  weakenICX (next pre) W (next x) = {! InCtx.next (weakenICX pre W x)  !}

  {-
  data Exp : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Exp {n} (Γ , A) B → Exp Γ (Π A B)
    cumu : ∀{Γ n T} → Exp {n} Γ T → Exp {suc n} Γ (cumu T)
    var : ∀{n Γ T} → InCtx {n} Γ T → Exp Γ T
    app : ∀{Γ n A B} → Exp {n} Γ (Π A B) → (a : Exp Γ A) → Exp {n} Γ {! subType a in B  !}
    fromT : ∀{Γ n} → Type n Γ → Exp Γ (type n) -- needed for e.g. applying id : ∀X . X → X  to a specific type.

  -- Normal form
  data Nf : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Nf {n} (Γ , A) B → Nf Γ (Π A B)
    cumu : ∀{Γ n T} → Nf {n} Γ T → Nf {suc n} Γ (cumu T)
    fromT : ∀{Γ n} → Type n Γ → Nf Γ (type n)
    -- Neutral form
    ne : ∀{n Γ T nOut TOut}
      → (x : InCtx {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Γ TOut

-- --                              T             ↓ outputN   ↓ output type
  data Args : ∀{n} → (Γ : Context) → Type n Γ → (nOut : ℕ) → Type nOut Γ
    → Set where
    none : ∀{n Γ T} → Args {n} Γ T n T
    one : ∀{n Γ A B nOut TOut}
      → (arg : Exp {n} Γ A)
      → Args Γ {! subType arg in B  !} nOut TOut
      → Args {n} Γ (Π A B) nOut TOut
    cumu : ∀{n Γ T nOut TOut}
      → Args {n} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut
  -}
