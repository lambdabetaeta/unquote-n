open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

data Type : Set where
  _⇒_ : Type → Type → Type
  bool : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : (Γ : Ctx) → Set where
  same : ∀{Γ T} → InCtx (Γ , T)
  next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)

Tat : ∀{Γ} → InCtx Γ → Type
Tat (same {Γ} {T}) = T
Tat (next icx) = Tat icx

Γat : ∀{Γ} → InCtx Γ → Ctx
Γat (same {Γ} {T}) = Γ
Γat (next icx) = Γat icx

data Exp : Ctx → Type → Set where
  var : ∀{Γ} → (icx : InCtx Γ) → Exp Γ (Tat icx)
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  true : ∀{Γ} → Exp Γ bool
  false : ∀{Γ} → Exp Γ bool
  if : ∀{Γ A} → Exp Γ bool → Exp Γ A → Exp Γ A → Exp Γ A

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = (x : InCtx Γ₁) → Σ (InCtx Γ₂) (λ x' → Tat x' ≡ Tat x)

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren ren = (next ren) , refl

liftRen : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same , refl
liftRen ren (next itc) = let (itc' , p) = ren itc
  in next itc' , p

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x , refl

weaken : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Exp Γ₁ T → Exp Γ₂ T
weaken {Γ₁} {Γ₂} ren (var icx) = let (icx' , p) = ren icx in
  subst (λ T → Exp Γ₂ T) p (var icx')
weaken ren (lambda e) = lambda (weaken (liftRen ren) e)
weaken ren (app e₁ e₂) = app (weaken ren e₁) (weaken ren e₂)
weaken ren true = true
weaken ren false = false
weaken ren (if e e₁ e₂) = if (weaken ren e) (weaken ren e₁) (weaken ren e₂)

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

mutual
  -- TODO: make a more descriptive name for this function
  GenExpType : ∀{T} → ArgCount T → Ctx → Set
  GenExpType (none {T}) Γ = Exp Γ T
  GenExpType (one {A} count) Γ
    = ((count : ArgCount A) → GenExpType count Γ) → GenExpType count Γ

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = (x : InCtx Γ₁) → Exp Γ₂ (Tat x)
  -- TODO: TODO: problem: this needs to output GenExp instead of Exp
  -- Why? TODO TODO TODO TODO

  GenExp : Ctx → Type → Set
  GenExp Γ T = ∀{Γ'} → Sub Γ Γ'
    → (count : ArgCount T) → GenExpType count Γ'
    -- → Exp Γ T → (count : ArgCount T) → GenExpType count Γ'

  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = (ctxType Γ) × (GenExp Γ T)

  liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
  liftSub sub same = var same
  liftSub sub (next itc) = weaken weaken1Ren (sub itc)


-- The presence of Sub kinda makes sense because with γ arg, unquote-n
-- basically is doing sub and normalize at same time
unquote-n : ∀{Γ T} → Exp Γ T → GenExp Γ T
unquote-n (var icx) sub count = {! sub icx  !}
unquote-n (lambda e) sub none = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one count)
  = λ a → unquote-n e {!   !} count
unquote-n (app e₁ e₂) sub count
  = (unquote-n e₁ sub (one count)) {! λ sub count → ?  !}
  -- = (unquote-n sub e₁ (one count)) λ count → unquote-n sub e₂ count
unquote-n true sub count = {!   !}
unquote-n false sub count = {!   !}
unquote-n (if e e₁ e₂) sub count = {!   !}

-- nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → GenExpType count Γ
-- nApp none e = e
-- nApp (one count) e = λ x → nApp count (app e (x none))

-- unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
--   → GenExpType count (reduceCtx Γ γ)
-- unquote-n (var icx) count γ = varCase icx count γ
-- unquote-n (lambda e) none γ
--   = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
-- unquote-n (lambda e) (one count) γ
--   = λ a → unquote-n e count (γ , just a)
-- unquote-n (app e₁ e₂) count γ
--   = (unquote-n e₁ (one count) γ) (λ count → unquote-n e₂ count γ) -- parametrized by count, Γ and γ fixed
-- unquote-n true none γ = true
-- unquote-n false none γ = false
-- unquote-n (if e e₁ e₂) count γ with unquote-n e none γ
-- ... | e' = {! e'  !}
