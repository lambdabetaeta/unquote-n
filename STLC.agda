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
-- ToType (one {A} count) Γ = (Exp Γ A) → ToType count Γ
ToType (one {A} count) Γ
  = ((count : ArgCount A) → (ToType count Γ)) → ToType count Γ
-- TODO: think about how the Γ arg really works here!!!

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  -- ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe (Exp (reduceCtx Γ γ) T))
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe ((count : ArgCount T) → ToType count (reduceCtx Γ γ)))
  -- ctxType (Γ , T) = ctxType Γ × ((count : ArgCount T) → ToType count Γ)

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

-- T = A → B → C,    count = 2
-- output type is      Exp (Γ , T) A → Exp (Γ , T) B → Exp (Γ , T) C
nVarApp : ∀{Γ T} → (count : ArgCount T) → ToType count (Γ , T)
nVarApp none = var same
-- e none : A, (nVarApp count γ) : B, var same : A → B
nVarApp (one none) = λ e → app (var same) (e none)
-- nVarApp (one (one none)) = λ e₁ e₂ → app (app (var same) (e₁ none)) (e₂ none)
nVarApp (one (one none)) = λ e₁ e₂ → app (nVarApp (one none) e₁) (e₂ none)
nVarApp (one (one (one none)))
  = λ e₁ e₂ e₃ → app (app (nVarApp (one none) e₁) (e₂ none)) (e₃ none)
nVarApp count = {! unquote-n   !}
-- nVarApp (one count) = λ e → {!  nVarApp count   !} --app (nVarApp count) (e none)

varCase : ∀{Γ} → (icx : InCtx Γ) → (count : ArgCount (Tat icx))
  → (γ : ctxType Γ) → ToType count (reduceCtx Γ γ)
-- varCase same none (γ , nothing) = var same
varCase same count (γ , nothing) = nVarApp count
varCase same count (γ , just e) = e count
varCase (next icx) count (γ , nothing) = {! varCase icx count γ  !} -- this needs weakening. Is this a design flaw, or something that must be the case in the unquote-n algorithm?
varCase (next icx) count (γ , just x) = varCase icx count γ

-- IDEA: the output context shouldn't be the same as input context generally!
-- anything contained in γ should be removed from output Γ
unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
  → ToType count (reduceCtx Γ γ)
unquote-n (var icx) count γ = varCase icx count γ
unquote-n (lambda e) none γ
  = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
unquote-n (lambda e) (one count) γ
  = λ a → unquote-n e count (γ , just a)
unquote-n (app e₁ e₂) count γ
  = (unquote-n e₁ (one count) γ) (λ count → unquote-n e₂ count γ) -- (unquote-n e₂ none γ)
unquote-n true none γ = true
unquote-n false none γ = false
unquote-n (if e e₁ e₂) count γ with unquote-n e none γ
... | e' = {! e'  !}

-- TODO: double check that some issue like the repeated variable issue from
-- racket isn't secretly happening here!
