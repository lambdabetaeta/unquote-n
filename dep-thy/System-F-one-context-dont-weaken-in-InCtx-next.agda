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
  data Context : Set where
    ∅ : Context
    _,_ : ∀{n} → (Γ : Context) → Type n Γ → Context

  data Type : ℕ → Context → Set where
    Π : ∀{n Γ} → (A : Type n Γ) → (Type n (Γ , A)) → Type n Γ
    cumu : ∀{n Γ} → Type n Γ → Type (suc n) Γ
    type : ∀{Γ} → (n : ℕ) → Type (suc n) Γ
    -- Var : ∀{Γ n} → InCtx Γ (type n) → Type (suc n) Γ
    Var : ∀{Γpre Γ n} → (pre : Pre Γpre Γ) → InCtx Γ pre (type n) → Type (suc n) Γ
    -- fromE : ∀{Γ n} → Nf Γ (type n) → Type n Γ -- If I ever use this, should be Nf, as even Exps need to use Nf's for types.

  data Pre : Context → Context → Set where
    same : ∀{Γ} → Pre Γ Γ
    next : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₂} → Pre Γ₁ Γ₂ → Pre Γ₁ (Γ₂ , T)

  data InCtx : ∀{n Γpre} → (Γ : Context) → (Pre Γpre Γ) → Type n Γpre → Set where
    same : ∀{n Γ T} → InCtx {n} (Γ , T) (next same) T
    next : ∀{n m Γpre Γ A} → {T : Type m Γ} → {pre : Pre Γpre Γ}
      → InCtx {n} Γ pre A → InCtx (Γ , T) (next pre) A

mutual
  --          ↓ ↓    ↓    ↓            ↓   These make the arguments to any weakening function, by specifying how the context is being weakened.
  weakenΓ : ∀{Γ Γpre n} → Pre Γpre Γ → Type n Γpre → Context
  weakenΓ (same {Γ}) T = Γ , T
  weakenΓ (next {_} {_} {_} {T} pre) A = weakenΓ pre A , weakenType pre A T

  weakenType : ∀{Γ Γpre n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → Type m Γ → Type m (weakenΓ pre W)
  weakenType pre W (Π A B) = Π (weakenType pre W A) (weakenType (next pre) W B)
  weakenType pre W (cumu T) = cumu (weakenType pre W T)
  weakenType pre W (type n) = type n
  weakenType pre W (Var pre₁ x) = {! Var _ (weakenICX pre W _ x)  !} -- Var (weakenICX pre W x)

  weakenTypeByPre : ∀{Γpre Γ n} → Pre Γpre Γ → Type n Γpre → Type n Γ
  weakenTypeByPre same T = T
  weakenTypeByPre (next {_} {_} {_} {W} pre) T
    = weakenType same W (weakenTypeByPre pre T)

  -- I think that weakenTypeInPreCtx is bad design. Alternate design:
  -- A function (Pre Γa Γ) → (Pre Γb Γ) → ((Pre Γa Γb) ⊎ (Pre Γb Γa))
  -- Then, can simply weaken one pre by another by using standard weakening
  -- functions. So e.g. weakenΓ instead of weakenPreLeftCtx.

  preCompare : ∀{Γ₁ Γ₂ Γ₃} → (Pre Γ₁ Γ₃) → (Pre Γ₂ Γ₃)
    → (Pre Γ₁ Γ₂ ⊎ Pre Γ₂ Γ₁)
  preCompare same pre₂ = inj₂ pre₂ -- NOTE that there is overlap if both are same.
  preCompare pre₁ same = inj₁ pre₁ -- They actually give the same anwer on overlap.
  preCompare (next pre₁) (next pre₂) = preCompare pre₁ pre₂ -- could resolve with four cases, for all four options.

  transPre : ∀{Γ₁ Γ₂ Γ₃} → (Pre Γ₁ Γ₂) → (Pre Γ₂ Γ₃) → Pre Γ₁ Γ₃
  transPre pre₁ same = pre₁
  transPre pre₁ (next pre₂) = next (transPre pre₁ pre₂)

  -- If Γw is a prefix of Γ, and Γ is weakened, what does that do to Γw?
  -- call this function to find out.
  weakenPreLeftCtx : ∀{Γ Γpre Γw n} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (toWeaken : Pre Γw Γ) → Context
  weakenPreLeftCtx {_} {_} {Γw} pre W toWeaken with preCompare pre toWeaken
  ... | inj₁ p = weakenΓ p W
  ... | inj₂ p = Γw

  weakenPre : ∀{Γ Γpre Γw n} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (toWeaken : Pre Γw Γ)
    → Pre (weakenPreLeftCtx pre W toWeaken) (weakenΓ pre W)
  weakenPre pre W toWeaken with preCompare pre toWeaken
  ... | inj₁ p = {!   !}
  ... | inj₂ p = {! toWeaken  !}

  weakenTypeInPreCtx : ∀{Γ Γpre Γw n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (toWeaken : Pre Γw Γ)
    → Type m Γw → Type m (weakenPreLeftCtx pre W toWeaken)
  weakenTypeInPreCtx = {!   !}

  weakenICX : ∀{Γ Γpre Γx n m T} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → (prex : Pre Γx Γ)
    → InCtx {m} Γ prex T
    → InCtx {m} {weakenPreLeftCtx pre W prex}
      (weakenΓ pre W) (weakenPre pre W prex) (weakenTypeInPreCtx pre W prex T) --(weakenType pre W T)
  weakenICX = {!   !}




  data InCtx' : ∀{n} → (Γ : Context) → Type n Γ → Set where
    var : ∀{Γ Γpre n} → {T : Type n Γpre} → (pre : Pre (Γpre , T) Γ)
      → InCtx' Γ (weakenTypeByPre (transPre (next same) pre) T )

  weakenICX' : ∀{n Γ Γpre T} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → InCtx' {n} Γ T
    → InCtx' (weakenΓ pre W) (weakenType pre W T)
  weakenICX' pre W (var pre₁) = var {! weakenPre pre W pre₁  !}

  {-
    IDEA of the method in this FILE: (I don't know if it will work, but I am trying:)
    NEVER put any weakening (or substitution) in datatypes, only in functions.
    The only place I'm sure this won't be possible is in app case of Exp.
  -}

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
