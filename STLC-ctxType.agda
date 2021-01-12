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

mutual
  -- partially unquoted Exp
  PUExp : ∀{T} → ArgCount T → Ctx → Set
  PUExp (none {T}) Γ = Exp Γ T
  PUExp (one {A} count) Γ
    = (GExp Γ A) → PUExp count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExp : Ctx → Type → Set
  GExp Γ T = (count : ArgCount T) → PUExp count Γ

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe (GExp (reduceCtx Γ γ) T))

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

nApp : ∀{Γ T} → Exp Γ T → GExp Γ T
nApp e none = e
nApp e (one count) = λ a → nApp (app e (a none)) count

varCase : ∀{Γ} → (x : InCtx Γ) → (γ : ctxType Γ)
  → GExp (reduceCtx Γ γ) (Tat x)
varCase same (γ , nothing) = nApp (var same)
varCase same (γ , just e) = e
varCase (next x) (γ , nothing) = {! varCase x γ  !} -- varCase x γ count (forget1ren ren)
varCase (next x) (γ , just e) = varCase x γ

unquote-n : ∀{Γ T} → Exp Γ T → (γ : ctxType Γ)
  -- (count : ArgCount T) → PUExp count (reduceCtx Γ γ)
  → GExp (reduceCtx Γ γ) T
unquote-n (var icx) γ = varCase icx γ
unquote-n (lambda e) γ none = lambda (unquote-n e (γ , nothing) none)
unquote-n (lambda e) γ (one count)
  = λ a → unquote-n e (γ , just a) count
unquote-n (app e₁ e₂) γ count
  = (unquote-n e₁ γ (one count)) (unquote-n e₂ γ)
unquote-n true γ none = true
unquote-n false γ none = false
unquote-n (if e e₁ e₂) γ = {!   !}
