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
  PUExp : ∀{T} → ArgCount T → Ctx → Set
  PUExp (none {T}) Γ = Exp Γ T
  PUExp (one {A} count) Γ
    = (GExp Γ A) → PUExp count Γ
    -- NOTE: the above APUExp CAN be GExp without termination issues.
    -- If I make than change, probably better to delete APUExp and just put the count arg in GExp.

  -- Exp that can be partially unquoted to any amount
  GExp : Ctx → Type → Set
  GExp Γ T = (count : ArgCount T) → PUExp count Γ

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = (x : InCtx Γ₁) → GExp Γ₂ (Tat x)

weakenGExp : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → GExp Γ₁ T → GExp Γ₂ T
weakenGExp ren g none = weaken ren (g none)
weakenGExp ren g (one none) = λ a → {!   !}
weakenGExp ren g (one count) = λ a → weakenGExp ren (λ c → g (one c) {! a  !} ) count

nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → PUExp count Γ
nApp none e = e
nApp (one count) e = λ x → nApp count (app e (x none))
  -- TODO: this might not be possible!!!
liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
liftSub sub same count = nApp count (var same)
liftSub sub (next itc) = weakenGExp weaken1Ren (sub itc)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → let (y , p) = s₁ x
  in let (z , q) = s₂ y
  in z , trans q p

-- transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
-- transSR sub ren x ren₂ = sub x (ren ∘ ren₂)
--
append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → GExp Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe (GExp (reduceCtx Γ γ)))

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

unquote-n : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → GExp Γ₂ T
unquote-n (var icx) sub = sub icx
unquote-n (lambda e) sub none = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one count)
  = λ a → unquote-n e (append1sub sub a) count
unquote-n (app e₁ e₂) sub count
  = unquote-n e₁ sub (one count) (λ count → unquote-n e₂ sub count)
unquote-n true sub = {!   !}
unquote-n false sub = {!   !}
unquote-n (if e e₁ e₂) sub = {!   !}
-- unquote-n (var icx) sub = sub icx
-- unquote-n (lambda e) sub ren none
--   = lambda (unquote-n e (liftSub sub) (liftRen ren) none)
-- unquote-n (lambda e) sub ren (one count)
--   = λ a → unquote-n e (append1sub sub {!   !} ) ren count
-- unquote-n (app e₁ e₂) sub ren count
--   = unquote-n e₁ sub ren (one count) (λ ren₁ count → unquote-n e₂ (transSR sub ren) ren₁ count)
-- unquote-n true sub ren none = true
-- unquote-n false sub ren none = false
-- unquote-n (if e e₁ e₂) = {!   !}
