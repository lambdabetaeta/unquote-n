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

  -- TODO: how do I enforce expanded normal form?
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

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

mutual
  -- formerly PUExp -- For example, maps (A ⇒ B ⇒ C) ↦ (Exp A → Exp B → Exp C)
  Sem : Ctx → Type → Set
  Sem Γ (A ⇒ B) = GExp Γ A → Sem Γ B
  Sem Γ base = Nf Γ base

  GExp : Ctx → Type → Set
  GExp Γ T = ∀{Γ'} → Ren Γ Γ' → Sem Γ' T

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → GExp Γ₂ T

mutual
  -- brings things into expanded eta form.
  -- perhaps wouldn't be necessary if Nf was designed as inherently expanded eta form?
  -- x : A ⇒ B  ↦  λ a . app x a
  nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  nApp {_} {A ⇒ B} e = λ g → nApp (app e (reify g))
  nApp {_} {base} e = ne e

  -- I may have overcomplicated this definition?
  reify : ∀{Γ T} → GExp Γ T → Nf Γ T
  reify {_} {A ⇒ B} g
    = lambda (reify (λ ren → g (forget1ren ren) λ ren₂ → nApp (var (ren₂ (ren same)))))
  reify {_} {base} g = g idRen

idSub : ∀{Γ} → Sub Γ Γ
idSub x ren = nApp (var (ren x))

liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
liftSub sub same ren = nApp (var (ren same))
liftSub sub (next x) ren = sub x (forget1ren ren)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x ren₂ = sub x (ren ∘ ren₂)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → GExp Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same ren = e ren
append1sub sub e (next x) ren = sub x ren

eval : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → Sem Γ₂ T
eval (var x) sub = sub x idRen
eval (lambda e) sub = λ a → eval e (append1sub sub a)
eval (app e₁ e₂) sub = (eval e₁ sub) (λ ren₁ → eval e₂ (transSR sub ren₁))
eval ⋆ sub = ⋆

normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
normalize e = reify (λ ren → eval e (transSR idSub ren))

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
