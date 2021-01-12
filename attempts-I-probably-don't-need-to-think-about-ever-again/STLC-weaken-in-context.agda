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

-- TODO: make a more descriptive name for this function
ToType : ∀{T} → ArgCount T → Ctx → Set
ToType (none {T}) Γ = Exp Γ T
ToType (one {A} count) Γ
  = (∀{Γ'} → (Ren Γ Γ')
      → (count' : ArgCount A)
      → (ToType count' Γ'))
    → ToType count Γ

  -- the above line passes termination check because A is structurally less than (A ⇒ B)
  -- Question: In system F, will type levels be necessary or can I do impredicative?
  -- If necessary, why and where do they come in? If not, what stopping me form doing impredicative dependent type theory (which is of course inconsistent?)

  -- TODO: TODO: PROBLEM:
  -- Anothing thing is that in dep thy, the r.h.s of the line
  -- will need to depend on the argument from the left!!!!!!
  -- Maybe it just is in a more general context?
  -- (I think system F is fine though, as that only happens when arg is
  -- ∀X, but then left side doesn't need to input count.)

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T)
    = Σ (ctxType Γ)
        (λ γ →
          Maybe (∀{Γ'} → Ren Γ Γ'
            → (count : ArgCount T) → ToType count (reduceCtx Γ' γ)))
  -- TODO: why is there code repetition here with ToType?

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

-- Simplify racket implementation to this!!!
nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → ToType count Γ
nApp none e = e
nApp (one count) e = λ x → nApp count (app e (x idRen none) )

varCase : ∀{Γ} → (icx : InCtx Γ) → (count : ArgCount (Tat icx))
  → (γ : ctxType Γ) → ToType count (reduceCtx Γ γ)
varCase same count (γ , nothing) = nApp count (var same)
varCase same count (γ , just e) = e count
varCase (next icx) count (γ , nothing) = {! (varCase icx count γ)  !} -- this needs weakening. Is this a design flaw, or something that must be the case in the unquote-n algorithm?
varCase (next icx) count (γ , just x) = varCase icx count γ

unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
  → ToType count (reduceCtx Γ γ)
unquote-n (var icx) count γ = varCase icx count γ
unquote-n (lambda e) none γ
  = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
unquote-n (lambda e) (one count) γ
  = {!   !}
  -- = λ a → unquote-n e count (γ , just a)
unquote-n (app e₁ e₂) count γ
  = (unquote-n e₁ (one count) γ) {!   !}
  -- = (unquote-n e₁ (one count) γ) (λ count → unquote-n e₂ count γ)
  -- IDEA: IDEA: include renaming arg after count, weaken BEFORE unquote!
unquote-n true none γ = true
unquote-n false none γ = false
unquote-n (if e e₁ e₂) count γ with unquote-n e none γ
... | e' = {! e'  !}
