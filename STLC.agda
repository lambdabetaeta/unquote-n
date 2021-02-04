open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : (Γ : Ctx) → Type → Set where
  same : ∀{Γ T} → InCtx (Γ , T) T
  next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

data Exp : Ctx → Type → Set where
  var : ∀{Γ T} → (icx : InCtx Γ T) → Exp Γ T
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  ⋆ : ∀{Γ} → Exp Γ base

mutual
  data Ne : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
    app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    ne : ∀{Γ T} → Ne Γ T → Nf Γ T
    ⋆ : ∀{Γ} → Nf Γ base

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → InCtx Γ₂ T

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren ren = next ren

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

liftRen : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same
liftRen ren (next itc) = next (ren itc)

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

weaken : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Exp Γ₁ T → Exp Γ₂ T
weaken {Γ₁} {Γ₂} ren (var icx) = var (ren icx)
weaken ren (lambda e) = lambda (weaken (liftRen ren) e)
weaken ren (app e₁ e₂) = app (weaken ren e₁) (weaken ren e₂)
weaken ren ⋆ = ⋆

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

mutual
  -- partially unquoted Exp
  PUExp : ∀{T} → ArgCount T → Ctx → Set
  PUExp (none {T}) Γ = Nf Γ T
  PUExp (one {A} count) Γ
    = (GExp Γ A) → PUExp count Γ
    -- NOTE: maybe in system F here, the R.H.S. can simply be in a larger Δ

  -- Exp that can be partially unquoted to any amount
  APUExp : Ctx → Type → Set
  APUExp Γ T = (count : ArgCount T) → PUExp count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExp : Ctx → Type → Set
  GExp Γ T = ∀{Γ'} → Ren Γ Γ' → APUExp Γ' T -- NOTE: the key was using Ren instead of Sub here!

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → GExp Γ₂ T

nApp : ∀{Γ T} → (count : ArgCount T) → Ne Γ T → PUExp count Γ
nApp none e = ne e
nApp (one count) e = λ x → nApp count (app e (x idRen none))

idSub : ∀{Γ} → Sub Γ Γ
idSub x ren count = nApp count (var (ren x))

liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
liftSub sub same ren count = nApp count (var (ren same))
liftSub sub (next itc) ren = sub itc (forget1ren ren)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x ren₂ = sub x (ren ∘ ren₂)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → GExp Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same ren = e ren
append1sub sub e (next x) ren = sub x ren

unquote-n : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → APUExp Γ₂ T
unquote-n (var icx) sub = sub icx idRen -- sub icx
unquote-n (lambda e) sub none
  = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one count)
  = λ a → unquote-n e (append1sub sub a) count
unquote-n (app e₁ e₂) sub count
  = unquote-n e₁ sub (one count) (λ ren₁ count → unquote-n e₂ (transSR sub ren₁) count)
unquote-n ⋆ sub none = ⋆

normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
normalize e = unquote-n e idSub none

-- some examples to test it out:

e1 : Exp ∅ base
e1 = app (lambda (var same)) ⋆

test1 : normalize e1 ≡ ⋆
test1 = refl

e2 : Exp ∅ base -- (λ x . x ⋆) (λ x . x)
e2 = app (lambda (app (var same) ⋆ )) (lambda (var same))

test2 : normalize e2 ≡ ⋆
test2 = refl

e3 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) ⋆
e3 = lambda (app (lambda (var same)) ⋆)

test3 : normalize e3 ≡ lambda ⋆
test3 = refl

e4 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) x
e4 = lambda (app (lambda (var same)) (var same))

test4 : normalize e4 ≡ lambda (ne (var same))
test4 = refl
