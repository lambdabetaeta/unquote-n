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
  PUExp : ∀{T} → ArgCount T → Ctx → Ctx → Set
  PUExp (none {T}) Γin Γout = Exp Γout T
  PUExp (one {A} count) Γin Γout
    = (GExp Γout Γin A) → PUExp count Γin Γout

  -- Exp that can be in a weaker context AND partially unquoted
  GExp : Ctx → Ctx → Type → Set
  GExp Γin Γout T = -- NOTE: covariant vs contravariant, Γin vs Γout in input vs output positions, so think about how < rule for function works!
    (count : ArgCount T) → PUExp count Γin Γout

  Sub : Ctx → Ctx → Ctx → Set
  Sub Γ Γin Γout = (x : InCtx Γ) → GExp Γin Γout (Tat x)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → let (y , p) = s₁ x
  in let (z , q) = s₂ y
  in z , trans q p

weakenGExp : ∀{Γin₁ Γin₂ Γout₁ Γout₂ T} → Ren Γin₂ Γin₁ → Ren Γout₁ Γout₂
  → GExp Γin₁ Γout₁ T → GExp Γin₂ Γout₂ T
weakenGExp renIn renOut g none = weaken renOut (g none)
weakenGExp renIn renOut g (one count)
  = λ a → let weakA = weakenGExp renOut renIn a
    in weakenGExp renIn renOut (λ count → g (one count) weakA) count

nApp : ∀{Γin Γout T} → Exp Γin T → GExp Γin Γout T
nApp e none = e
nApp e (one count) = λ a → nApp (app e {! a none  !} ) count

liftSub : ∀{Γ Γin Γout T} → Sub Γ Γin Γout → Sub (Γ , T) Γin (Γout , T)
liftSub sub same = nApp (var same)
liftSub sub (next x) = weakenGExp idRen weaken1Ren (sub x)
-- liftSub sub same ren count
--   = {! nApp count   !}
--   -- = nApp count let (y , p) = ren same in subst (λ T → Exp _ T) p (var y) -- define using nApp!!!!!!!!!
-- liftSub sub (next itc) ren count = {! sub itc ren   !} -- sub itc (forget1ren ren)

append1sub : ∀{Γ A Γin Γout} → Sub Γ Γin Γout → GExp Γin Γout A → Sub (Γ , A) Γin Γout
append1sub sub e same = e
append1sub sub e (next x) = sub x
-- append1sub sub e same ren = e ren
-- append1sub sub e (next x) ren = sub x ren

mutual
  unquote-n : ∀{Γ Γin Γout T} → Exp Γ T
    → Sub Γ Γin Γout
    → GExp Γin Γout T
  unquote-n (var icx) sub = sub icx
  unquote-n (lambda e) sub none = lambda (unquote-n e (liftSub sub) none)
  unquote-n (lambda e) sub (one count)
    = λ a → unquote-n e (append1sub sub {! a  !} ) count
  unquote-n (app e₁ e₂) sub count
    = unquote-n e₁ sub (one count) (λ count → unquote-n e₂ {! sub  !} count)
  unquote-n true sub none = true
  unquote-n false sub none = false
  unquote-n (if e e₁ e₂) sub = {!   !}

{-
NOTE:

Inputs from functions and inputs from context should be the same, but
Inputs in functions have Γin and Γout switched, while inputs in context
don't.
-}
