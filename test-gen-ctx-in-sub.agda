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

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = (x : InCtx Γ₁) → ∀{Γ'} → Ren Γ₂ Γ' → GExp Γ' (Tat x)

-- weakenC : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Exp Γ₁ T → Exp Γ₂ T

nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → PUExp count Γ
nApp none e = e
nApp (one count) e = λ x → nApp count (app e (x none))

liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
liftSub sub same ren count = nApp count let (y , p) = ren same in subst (λ T → Exp _ T) p (var y)
liftSub sub (next itc) ren = sub itc (forget1ren ren)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → (∀{Γ'} → Ren Γ₂ Γ' → GExp Γ' A) → Sub (Γ₁ , A) Γ₂
append1sub sub e same ren count = e ren count -- e ren
append1sub sub e (next x) ren = sub x ren

unquote-n : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → GExp Γ₂ T
unquote-n (var icx) sub = sub icx idRen -- sub icx
unquote-n (lambda e) sub none
  = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one count)
  = λ a → unquote-n e (append1sub sub {! a  !} ) count
unquote-n (app e₁ e₂) sub count
  = unquote-n e₁ sub (one count) (unquote-n e₂ sub)
unquote-n true sub none = true
unquote-n false sub none = false
unquote-n (if e e₁ e₂) = {!   !}
-- unquote-n (lambda e) sub none = lambda (unquote-n e {!   !} none)
-- unquote-n (lambda e) sub (one count) = λ a → unquote-n e {!   !} count
-- unquote-n (app e₁ e₂) sub count
--   = (unquote-n e₁ sub (one count)) (unquote-n e₂ sub)
-- unquote-n true = {!   !}
-- unquote-n false = {!   !}
-- unquote-n (if e e₁ e₂) = {!   !}
