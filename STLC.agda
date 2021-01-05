open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe

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

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

ToType : ∀{T} → ArgCount T → Ctx → Set
ToType (none {T}) Γ = Exp Γ T
ToType (one {A} count) Γ = (Exp Γ A) → ToType count Γ
-- TODO: think about how the Γ arg really works here!!!

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe (Exp (reduceCtx Γ γ) T))
  -- ctxType (Γ , T) = ctxType Γ × ((count : ArgCount T) → ToType count (reduceCtx Γ γ))
  -- ctxType (Γ , T) = ctxType Γ × ((count : ArgCount T) → ToType count Γ)

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

-- IDEA: the output context shouldn't be the same as input context generally!
-- anything contained in γ should be removed from output Γ
unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
  → ToType count (reduceCtx Γ γ)
unquote-n {Γ , T} (var same) count (γ , nothing) = {!   !}
unquote-n {Γ , T} (var same) none (γ , just e) = e -- IDEA: make ctxType not just have Exp, but actually (count : ArgCount)  to ToType count (reduceCtx Γ γ), so that more than just none case works!!!
unquote-n {Γ , .(_ ⇒ _)} (var same) (one count) (γ , just e) = {!   !}
unquote-n {Γ , T} (var (next icx)) count γ = {!   !}
unquote-n (lambda e) none γ
  = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
  -- = lambda (unquote-n e none {!   !} )
unquote-n (lambda e) (one count) γ
  = λ a → unquote-n e count (γ , just a)
  -- = λ a → unquote-n e count (γ , a)
unquote-n (app e₁ e₂) count γ
  -- = (unquote-n e₁ (one count) γ) e₂
  = (unquote-n e₁ (one count) γ) (unquote-n e₂ none γ)
unquote-n true none γ = true
unquote-n false none γ = false
unquote-n (if e e₁ e₂) count γ = {!   !}

-- TODO: double check that some issue like the repeated variable issue from
-- racket isn't secretly happening here!
