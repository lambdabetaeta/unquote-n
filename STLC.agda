open import Data.Unit
open import Data.Product
open import Data.Bool
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
Ren Δ Γ = ∀{T} → InCtx Γ T → InCtx Δ T

weaken1Ren : ∀{Γ T} → Ren (Γ , T) Γ
weaken1Ren ren = next ren

forget1ren : ∀{Δ Γ T} → Ren Δ (Γ , T) → Ren Δ Γ
forget1ren ren x = ren (next x)

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

mutual
  -- partially unquoted Exp
  PUExp : ∀{T} → ArgCount T → Ctx → Set
  PUExp (none {T}) Γ = Nf Γ T
  PUExp (one {A} count) Γ = (GExp Γ A) → PUExp count Γ

  -- Exp that can be in a weaker context AND partially unquoted to any degree
  GExp : Ctx → Type → Set
  GExp Γ T = ∀{Γ'} → Ren Γ' Γ → (count : ArgCount T) → PUExp count Γ'

Sub : Ctx → Ctx → Set
Sub Δ Γ = ∀{T} → InCtx Γ T → GExp Δ T

append1sub : ∀{Δ Γ A} → Sub Δ Γ → GExp Δ A → Sub Δ (Γ , A)
append1sub sub e same ren = e ren
append1sub sub e (next x) ren = sub x ren

nApp : ∀{Γ T} → (count : ArgCount T) → Ne Γ T → PUExp count Γ
nApp none e = ne e
nApp (one count) e = λ x → nApp count (app e (x idRen none))

idSub : ∀{Γ} → Sub Γ Γ
idSub x ren count = nApp count (var (ren x))

liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
liftSub sub same ren count = nApp count (var (ren same))
liftSub sub (next itc) ren = sub itc (forget1ren ren)

_∘_ : ∀{Θ Δ Γ} → Ren Θ Δ → Ren Δ Γ → Ren Θ Γ
s₁ ∘ s₂ = λ x → s₁ (s₂ x)

transSR : ∀{Θ Δ Γ} → Sub Δ Γ → Ren Θ Δ → Sub Θ Γ
transSR sub ren x ren₂ = sub x (ren₂ ∘ ren)

unquote-n : ∀{Γ Δ T} → Exp Γ T → Sub Δ Γ → (count : ArgCount T) → PUExp count Δ
unquote-n (var icx) sub = sub icx idRen
unquote-n (lambda e) sub none = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one count) = λ a → unquote-n e (append1sub sub a) count
unquote-n (app e₁ e₂) sub count = unquote-n e₁ sub (one count) (λ ren₁ count → unquote-n e₂ (transSR sub ren₁) count)
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
