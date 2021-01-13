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

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

liftRen : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same , refl
liftRen ren (next itc) = let (itc' , p) = ren itc
  in next itc' , p

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x , refl

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → let (y , p) = s₁ x
  in let (z , q) = s₂ y
  in z , trans q p

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

-- TODO: make a more descriptive name for this function
ToType : ∀{T} → ArgCount T → Ctx → Set
ToType (none {T}) Γ = Exp Γ T
ToType (one {A} count) Γ
  -- = ((count' : ArgCount A) → (ToType count' Γ)) → ToType count Γ
  = ToType count (Γ , A)

weakenToType : ∀{T Γ₁ Γ₂} → (count : ArgCount T)
  → Ren Γ₁ Γ₂
  → ToType count Γ₁ → ToType count Γ₂
weakenToType none ren e = weaken ren e
weakenToType (one count) ren e = weakenToType count (liftRen ren) e

GExp : Ctx → Type → Set
GExp Γ A = (count : ArgCount A) → ToType count Γ

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe (GExp (reduceCtx Γ γ) T))

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → ToType count Γ
nApp none e = e
nApp (one count) e = nApp count (app (weaken weaken1Ren e) (var same))

varCase : ∀{Γ} → (icx : InCtx Γ) → (count : ArgCount (Tat icx))
  → (γ : ctxType Γ) → ToType count (reduceCtx Γ γ)
varCase same count (γ , nothing) = nApp count (var same)
varCase same count (γ , just e) = e count
varCase (next icx) count (γ , nothing) = weakenToType count weaken1Ren (varCase icx count γ) -- this needs weakening. Is this a design flaw, or something that must be the case in the unquote-n algorithm?
varCase (next icx) count (γ , just x) = varCase icx count γ

unquote-n : ∀{Γ T} → Exp Γ T → (γ : ctxType Γ)
  → GExp (reduceCtx Γ γ) T
unquote-n (var icx) γ count = varCase icx count γ
unquote-n (lambda e) γ none
  = lambda (unquote-n e (γ , nothing) none)
unquote-n (lambda e) γ (one count)
  = unquote-n e (γ , {!   !} ) {!   !}
unquote-n (app e e₁) γ = {!   !}
unquote-n true γ = {!   !}
unquote-n false γ = {!   !}
unquote-n (if e e₁ e₂) γ = {!   !}

-- unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
--   → ToType count (reduceCtx Γ γ)
-- unquote-n (var icx) count γ = varCase icx count γ
-- unquote-n (lambda e) none γ
--   = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
-- unquote-n (lambda e) (one count) γ
--   = λ a → unquote-n e count (γ , just a)
-- unquote-n (app e₁ e₂) count γ
--   = (unquote-n e₁ (one count) γ) (λ count → unquote-n e₂ count γ) -- parametrized by count, Γ and γ fixed
-- unquote-n true none γ = true
-- unquote-n false none γ = false
-- unquote-n (if e e₁ e₂) = {!   !}
