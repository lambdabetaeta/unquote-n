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

data Pre : Ctx → Set where
  same : ∀{Γ} → Pre Γ
  next : ∀{Γ T} → Pre Γ → Pre (Γ , T)

toCtx : ∀{Γ} → Pre Γ → Ctx
toCtx (same {Γ}) = Γ
toCtx (next pre) = toCtx pre

weakenΓ : ∀{Γ} → Pre Γ → Type → Ctx
weakenΓ (same {Γ}) A = Γ , A
weakenΓ (next {Γ} {T} pre) A = (weakenΓ pre A) , T

weakenICX : ∀{Γ} → (pre : Pre Γ) → (W : Type)
  → (icx : InCtx Γ) → Σ (InCtx (weakenΓ pre W)) (λ icx' → Tat icx' ≡ Tat icx)
weakenICX same W icx = next icx , refl
weakenICX (next pre) W same = same , refl
weakenICX (next pre) W (next icx) with weakenICX pre W icx
...                               | (i , p) = (next i , p)

weaken : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → Exp Γ T → Exp (weakenΓ pre W) T
weaken pre W (var icx) with weakenICX pre W icx
...                    | (i , p) = subst (λ T → Exp _ T) p (var i)
weaken pre W (lambda e) = lambda (weaken (next pre) W e)
weaken pre W (app e₁ e₂) = app (weaken pre W e₁) (weaken pre W e₂)
weaken pre W true = true
weaken pre W false = false
weaken pre W (if e e₁ e₂) = if (weaken pre W e) (weaken pre W e₁) (weaken pre W e₂)

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

-- TODO: make a more descriptive name for this function
ToType : ∀{T} → ArgCount T → Ctx → Set
ToType (none {T}) Γ = Exp Γ T
ToType (one {A} count) Γ
  = ((count' : ArgCount A) → (ToType count' Γ)) → ToType count Γ
  -- = ((Ren Γ Γ') → (count' : ArgCount A) → (ToType count' Γ'))
      -- → ToType count Γ
  -- (1)


  -- the above line passes termination check because A is structurally less than (A ⇒ B)
  -- Question: In system F, will type levels be necessary or can I do impredicative?
  -- If necessary, why and where do they come in? If not, what stopping me form doing impredicative dependent type theory (which is of course inconsistent?)

  -- TODO: TODO: PROBLEM:
  -- Anothing thing is that in dep thy, the r.h.s of the line
  -- will need to depend on the argument from the left!!!!!!
  -- Maybe it just is in a more general context?
  -- (I think system F is fine though, as that only happens when arg is
  -- ∀X, but then left side doesn't need to input count.)

-- weakenToType : ∀{Γ T} → (count : ArgCount T) → (pre : Pre Γ) → (W : Type)
--   → ToType count Γ → ToType count (weakenΓ pre W)
-- weakenToType none pre W e = weaken pre W e
-- weakenToType (one count) pre W e
--   = λ x → weakenToType count pre W {! e x  !}

-- Exp Γ A → Exp Γ B
-- Exp Γ' A → Exp Γ' B

mutual
  ctxType : Ctx → Set
  ctxType ∅ = ⊤
  ctxType (Γ , T) = Σ (ctxType Γ) (λ γ → Maybe ((count : ArgCount T) → ToType count (reduceCtx Γ γ)))

  reduceCtx : (Γ : Ctx) → ctxType Γ → Ctx
  reduceCtx ∅ tt = ∅
  reduceCtx (Γ , T) (γ , nothing) = reduceCtx Γ γ , T
  reduceCtx (Γ , T) (γ , just e) = reduceCtx Γ γ

-- Simplify racket implementation to this!!!
nApp : ∀{Γ T} → (count : ArgCount T) → Exp Γ T → ToType count Γ
nApp none e = e
nApp (one count) e = λ x → nApp count (app e (x none))

varCase : ∀{Γ} → (icx : InCtx Γ) → (count : ArgCount (Tat icx))
  → (γ : ctxType Γ) → ToType count (reduceCtx Γ γ)
varCase same count (γ , nothing) = nApp count (var same)
varCase same count (γ , just e) = e count
varCase (next icx) count (γ , nothing) = {! (varCase icx count γ)  !} -- this needs weakening. Is this a design flaw, or something that must be the case in the unquote-n algorithm?
varCase (next icx) count (γ , just x) = varCase icx count γ
-- (3)

unquote-n : ∀{Γ T} → Exp Γ T → (count : ArgCount T) → (γ : ctxType Γ)
  → ToType count (reduceCtx Γ γ)
unquote-n (var icx) count γ = varCase icx count γ
unquote-n (lambda e) none γ
  = lambda (unquote-n e none (γ , nothing)) -- e is in context Γ , A
unquote-n (lambda e) (one count) γ
  = λ a → unquote-n e count (γ , just a)
unquote-n (app e₁ e₂) count γ
  = (unquote-n e₁ (one count) γ) (λ count → unquote-n e₂ count γ) -- parametrized by count, Γ and γ fixed
  -- (2)
unquote-n true none γ = true
unquote-n false none γ = false
unquote-n (if e e₁ e₂) = {!   !}



-- Some evaluation works even without the missing case
code : Exp ∅ bool
code = app (lambda (var same)) true

res : (unquote-n code none tt) ≡ true
res = refl

code2 : Exp ∅ (bool ⇒ bool)
code2 = lambda (app (lambda (var same)) true)

res2 : (unquote-n code2 none tt) ≡ (lambda true)
res2 = refl

code3 : Exp ∅ (bool ⇒ bool)
code3 = app (lambda (lambda (var same))) true

res3 : (unquote-n code3 none tt) ≡ (lambda (var same))
res3 = refl

code4 : Exp ∅ (bool ⇒ (bool ⇒ bool))
code4 = lambda (lambda (var same))

res4 : (unquote-n code4 none tt) ≡ code4
res4 = refl

code5 : Exp ∅ (bool ⇒ bool)
code5 = app (lambda (lambda (var (next same)))) true

-- NOTE: that in this case, the true is actually in a smaller context.
-- So it would work to weaken only after applying the function of type ToType count
res5 : (unquote-n code5 none tt) ≡ (lambda true)
res5 = {!   !}
