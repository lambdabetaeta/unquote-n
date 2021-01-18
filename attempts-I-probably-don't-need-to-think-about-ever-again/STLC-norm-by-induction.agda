open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Sum

data Type : Set where
  _⇒_ : Type → Type → Type
  bool : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : Ctx → Type → Set where
  same : ∀{Γ T} → InCtx (Γ , T) T
  next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

mutual
  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    true : ∀{Γ} → Nf Γ bool
    false : ∀{Γ} → Nf Γ bool
    if : ∀{Γ A} → Nf Γ bool → Nf Γ A → Nf Γ A → Nf Γ A
    fromNe : ∀{Γ T} → Ne Γ T → Nf Γ T

  data Ne : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
    app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → InCtx Γ₂ T

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren ren = next ren

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

liftRen : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same
liftRen ren (next x) = next (ren x)

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

mutual
  weakenNf : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Nf Γ₁ T → Nf Γ₂ T
  weakenNf ren (lambda e) = lambda (weakenNf (liftRen ren) e)
  weakenNf ren true = true
  weakenNf ren false = false
  weakenNf ren (if e e₁ e₂) = if (weakenNf ren e) (weakenNf ren e₁) (weakenNf ren e₂)
  weakenNf ren (fromNe e) = fromNe (weakenNe ren e)
  weakenNe : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ne Γ₁ T → Ne Γ₂ T
  weakenNe ren (var icx) = var (ren icx)
  weakenNe ren (app e₁ e₂) = app (weakenNe ren e₁) (weakenNf ren e₂)

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

inputs : ∀{T} → ArgCount T → Ctx → Set
inputs none Γ = ⊤
inputs (one {A} count) Γ = Nf Γ A × inputs count Γ

output : ∀{T} → ArgCount T → Type
output (none {T}) = T
output (one count) = output count

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → (x : InCtx Γ₁ T) → Nf Γ₂ T

append1sub : ∀{Γ A} → Nf Γ A → Sub (Γ , A) Γ
append1sub e same = e
append1sub e (next x) = fromNe (var x)

liftSub : ∀{Γ₁ Γ₂ A} → Sub Γ₁ Γ₂ → Sub (Γ₁ , A) (Γ₂ , A)
liftSub sub same = fromNe (var same)
liftSub sub (next x) = weakenNf weaken1Ren (sub x)

nApp : ∀{Γ T} → (count : ArgCount T) → inputs count Γ
    → Ne Γ T → Ne Γ (output count)
nApp none inputs e = e
nApp (one count) (a , inputs) e = nApp count inputs (app e a)

neVarType : ∀{Γ T} → Ne Γ T → Type
neVarType (var {Γ} {T} icx) = T
neVarType (app e x) = neVarType e

-- neCount : ∀{Γ T} → Ne Γ T → Type
-- neCount : ∀{Γ}

mutual
  substitute : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Nf Γ₁ T → Nf Γ₂ T
  substitute sub (lambda e) = lambda (substitute (liftSub sub) e)
  substitute sub true = true
  substitute sub false = false
  substitute sub (if e e₁ e₂) = {!   !}
  substitute sub (fromNe e) = substituteNe sub e

  substituteNe : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Ne Γ₁ T → Nf Γ₂ T
  substituteNe sub (var icx) = sub icx
  substituteNe sub (app e₁ e₂)
    = let e₁' = substituteNe sub e₁
      in let e₂' = substitute sub e₂
      -- Here we are calling apply on (A ⇒ T), which is LARGER than T
      -- This is the purpose of varapp
      -- That being said, an Ne is pretty much like a varapp, so maybe
      -- with the right induction, can work?
      -- like make function Ne -> (icx at left , list of args)
      -- then call app!
      -- the fact were not subbing one var might hurt?
      in {! apply (one none) (e₂' , tt) e₁'  !} -- apply (one none) (e₂' , tt) e₁'
      -- in fromNe {! apply (one none) (e₂ , tt) (fromNe e₁)   !}

  apply : ∀{Γ T} → (count : ArgCount T) → inputs count Γ
    → Nf Γ T → Nf Γ (output count)
  apply none inputs (lambda e) = lambda e
  apply (one count) (a , inputs) (lambda e)
    = let e' = substitute (append1sub a) e
      in apply count inputs e'
  apply none inputs true = true
  apply none inputs false = false
  apply count inputs (if e e₁ e₂) = {!   !}
  apply count inputs (fromNe e) = fromNe (nApp count inputs e)
