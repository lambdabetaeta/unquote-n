-- TODO: should I use cumulativity?
{-# OPTIONS --cumulativity --without-K #-}

open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)
open import Data.List
open import Agda.Primitive
open import Data.Unit

-- TCtx l represents context of a type at level l,
-- which will only include type of up to level (l - 1)
-- because Fin n = {0 ,  ... , n-1}

data Lev : Set where
  l0 l1 l2 : Lev

maxLevel = lsuc (lsuc (lsuc lzero))

Setn : Lev → Set maxLevel
Setn l0 = Set₀
Setn l1 = Set₁
Setn l2 = Set₂

data TCtx : Set where
  ∅ : TCtx
  _,_ : TCtx → Lev → TCtx

-- TCtxCumu : ∀{l₁ l₂} → l₁ ≤ l₂ → TCtx l₁ → TCtx l₂
-- TCtxCumu z≤n Δ = {!   !}
-- TCtxCumu (s≤s p) Δ = {!   !}


data InTCtx : TCtx → Lev → Set where
  same : ∀{Δ n} → InTCtx (Δ , n) n
  next : ∀{Δ n m} → InTCtx Δ n → InTCtx (Δ , m) n

TRen : TCtx → TCtx → Set
TRen Δ₁ Δ₂ = ∀{n} → InTCtx Δ₁ n → InTCtx Δ₂ n

weaken1Δ : ∀{Δ n} → TRen Δ (Δ , n)
weaken1Δ ren = next ren

liftTRen : ∀{Δ₁ Δ₂ n} → TRen Δ₁ Δ₂ → TRen (Δ₁ , n) (Δ₂ , n)
liftTRen ren same = same
liftTRen ren (next itc) = next (ren itc)

-- represents a type at level l
data Type : Lev → TCtx →  Set where
  Var₀ : ∀{Δ} → InTCtx Δ l0 → Type l0 Δ
  Var₁ : ∀{Δ} → InTCtx Δ l1 → Type l1 Δ
  Var₂ : ∀{Δ} → InTCtx Δ l2 → Type l2 Δ
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
  ⋁₀ : ∀{Δ} → Type l1 (Δ , l0) → Type l1 Δ
  ⋁₁ : ∀{Δ} → Type l2 (Δ , l1) → Type l2 Δ
  cumu₀ : ∀{Δ} → Type l0 Δ → Type l1 Δ
  cumu₁ : ∀{Δ} → Type l1 Δ → Type l2 Δ

renType : ∀{n Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
renType = {!   !}
-- renType ren (Var x) = Var (ren x)
-- renType ren (A ⇒ B) = renType ren A ⇒ renType ren B
-- renType ren (⋁ T) = ⋁ (renType (liftTRen ren) T)
-- renType ren (cumu T) = cumu (renType ren T)

data Ctx : TCtx → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{n Δ} → Ctx Δ → Type n Δ → Ctx Δ

renΓ : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renΓ ren ∅ = ∅
renΓ ren (Γ , T) = renΓ ren Γ , renType ren T

data InCtx : ∀{n Δ} → (Γ : Ctx Δ) → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ Γ A} → {T : Type m Δ}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = ∀{n} → InTCtx Δ₁ n → Type n Δ₂

idSub : ∀{Δ} → TSub Δ Δ
idSub {_} {l0} x = Var₀ x
idSub {_} {l1} x = Var₁ x
idSub {_} {l2} x = Var₂ x

append1sub : ∀{n Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Type n Δ₂ → TSub (Δ₁ , n) Δ₂
append1sub sub T same = T
append1sub sub T (next x) = sub x

liftTSub : ∀{Δ₁ Δ₂ n} → TSub Δ₁ Δ₂ → TSub (Δ₁ , n) (Δ₂ , n)
liftTSub {_} {_} {l0} sub same = Var₀ same
liftTSub {_} {_} {l1} sub same = Var₁ same
liftTSub {_} {_} {l2} sub same = Var₂ same
liftTSub {_} {_} {n} sub (next x) = renType weaken1Δ (sub x)

subType : ∀{n Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
-- subType sub (Var x) = sub x
-- subType sub (A ⇒ B) = subType sub A ⇒ subType sub B
-- subType sub (⋁ T) = ⋁ (subType (liftTSub sub) T)
-- subType sub (cumu T) = cumu (subType sub T)

data Exp : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
  var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{n Δ Γ A B} → Exp {n} Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Tlambda₀ : ∀{Δ Γ T}
    → Exp (Δ , l0) (renΓ weaken1Δ Γ) T → Type l0 Δ → Exp Δ Γ (⋁₀ T)
  Tlambda₁ : ∀{Δ Γ T}
    → Exp (Δ , l1) (renΓ weaken1Δ Γ) T → Type l1 Δ → Exp Δ Γ (⋁₁ T)
  TApp₀ : ∀{Δ Γ} → {T : Type l1 (Δ , l0)}
    → Exp Δ Γ (⋁₀ T)
    → (X : Type l0 Δ)
    → Exp Δ Γ (subType (append1sub idSub X) T)
  TApp₁ : ∀{Δ Γ} → {T : Type l2 (Δ , l1)}
    → Exp Δ Γ (⋁₁ T)
    → (X : Type l1 Δ)
    → Exp Δ Γ (subType (append1sub idSub X) T)
  cumu₀ : ∀{Δ T Γ}
    → Exp {l0} Δ Γ T
    → Exp {l1} Δ Γ (cumu₀ T)
  cumu₁ : ∀{Δ T Γ}
    → Exp {l1} Δ Γ T
    → Exp {l2} Δ Γ (cumu₁ T)

Ren : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Ren Γ₁ Γ₂ = ∀{n T} → InCtx Γ₁ T → InCtx {n} Γ₂ T

weaken1Ren : ∀{n Δ Γ} → {T : Type n Δ} → Ren Γ (Γ , T)
weaken1Ren ren = next ren

forget1ren : ∀{n Δ Γ₁ Γ₂} → {T : Type n Δ} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

liftRen : ∀{n Δ Γ₁ Γ₂} → {T : Type n Δ} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same
liftRen ren (next itc) = next (ren itc)

idRen : ∀{Δ Γ} → Ren {Δ} Γ Γ
idRen x = x

data Ne : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set
data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
  lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
  ne : ∀{n Δ Γ T} → Ne {n} Δ Γ T → Nf Δ Γ T
  Tlambda₀ : ∀{Δ Γ T}
    → Nf (Δ , l0) (renΓ weaken1Δ Γ) T → Type l0 Δ → Nf Δ Γ (⋁₀ T)
  Tlambda₁ : ∀{Δ Γ T}
    → Nf (Δ , l1) (renΓ weaken1Δ Γ) T → Type l1 Δ → Nf Δ Γ (⋁₁ T)
  cumu₀ : ∀{Δ T Γ}
    → Nf {l0} Δ Γ T
    → Nf {l1} Δ Γ (cumu₀ T)
  cumu₁ : ∀{Δ T Γ}
    → Nf {l1} Δ Γ T
    → Nf {l2} Δ Γ (cumu₁ T)

data Ne where
  var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Ne Δ Γ T
  TApp₀ : ∀{Δ Γ} → {T : Type l1 (Δ , l0)}
    → Ne Δ Γ (⋁₀ T)
    → (X : Type l0 Δ)
    → Ne Δ Γ (subType (append1sub idSub X) T)
  TApp₁ : ∀{Δ Γ} → {T : Type l2 (Δ , l1)}
    → Ne Δ Γ (⋁₁ T)
    → (X : Type l1 Δ)
    → Ne Δ Γ (subType (append1sub idSub X) T)
  app : ∀{n Δ Γ A B} → Ne {n} Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B

unquoteTCtx : TCtx → Set maxLevel
-- unquoteTCtx ∅ = ⊤
-- unquoteTCtx (Δ , n) = _×_ {maxLevel} {maxLevel} (unquoteTCtx Δ)  (Setn n)
unquoteTCtx Δ = ∀{n} → InTCtx Δ n → Setn n

append1δ : ∀{Δ n} → unquoteTCtx Δ → Setn n → unquoteTCtx (Δ , n)
append1δ δ X same = X
append1δ δ X (next x) = δ x

unquoteT : ∀{n Δ} → Type n Δ → (unquoteTCtx Δ → Set maxLevel)
unquoteT (Var₀ x) δ = δ x
unquoteT (Var₁ x) δ = δ x
unquoteT (Var₂ x) δ = δ x
unquoteT (A ⇒ B) δ = unquoteT A δ → unquoteT B δ
unquoteT (⋁₀ T) δ = (X : Set₀) → unquoteT T (append1δ δ X)
unquoteT (⋁₁ T) δ = (X : Set₁) → unquoteT T (append1δ δ X)
unquoteT (cumu₀ T) δ = unquoteT T δ
unquoteT (cumu₁ T) δ = unquoteT T δ

unquoteT₀ : ∀{Δ} → Type l0 Δ → (unquoteTCtx Δ → Set₀)
unquoteT₀ (Var₀ x) δ = δ x
unquoteT₀ (A ⇒ B) δ = unquoteT₀ A δ → unquoteT₀ B δ

-- nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
-- nApp {_} {A ⇒ B} e = λ g → nApp (app e (reify g))
-- nApp {_} {base} e = ne e

-- reify : ∀{Γ T} → GExp Γ T → Nf Γ T
-- reify {_} {A ⇒ B} g
--   = lambda (reify (λ ren → g (forget1ren ren) λ ren₂ → nApp (var (ren₂ (ren same)))))
-- reify {_} {base} g = g idRen

subType sub T = {!   !}
-- IDEA: if we can reify, then we can use unquoting to define subs.
-- Sem for (∀ X . T) should be Type → Type
-- already is with contexts, but things in contexts should be Type, not Set.
subEnd : ∀{Δ n m} → Type n Δ → Type m Δ → Type n (Δ , m)
subEnd T A = {!   !}

semΔ : Lev → TCtx → Set maxLevel
semΔ n ∅ = Type n ∅
semΔ n (Δ , l) = Type l Δ → semΔ n Δ

unquoteTalt : ∀{n Δ} → Type n Δ → semΔ n Δ
unquoteTalt {n} {∅} T = T
unquoteTalt {n} {Δ , x} T = λ A → unquoteTalt {!   !}

unquoteCtx : ∀{Δ} → Ctx Δ → unquoteTCtx Δ → Set maxLevel
unquoteCtx Γ δ = ∀{n T} → (InCtx {n} Γ T) → unquoteT T δ

append1γ : ∀{n Δ Γ T} → (δ : unquoteTCtx Δ)
  → unquoteCtx {Δ} Γ δ → unquoteT {n} T δ → unquoteCtx (Γ , T) δ
append1γ δ γ t same = t
append1γ δ γ t (next x) = γ x

unquoteExp : ∀{n Δ Γ T} → Exp {n} Δ Γ T → (δ : unquoteTCtx Δ)
  → unquoteCtx Γ δ → unquoteT T δ
unquoteExp (var x) δ γ = {!   !}
unquoteExp (lambda e) δ γ = λ a → unquoteExp e δ (append1γ δ γ a)
unquoteExp (app e₁ e₂) δ γ = (unquoteExp e₁ δ γ) (unquoteExp e₂ δ γ)
unquoteExp (Tlambda₀ e x) δ γ = λ X → unquoteExp e (append1δ δ X) {!   !}
unquoteExp (Tlambda₁ e x) δ γ = λ X → unquoteExp e (append1δ δ X) {!   !}
unquoteExp (TApp₀ e X) δ γ = {! (unquoteExp e δ γ) (unquoteT₀ X δ)  !}
unquoteExp (TApp₁ e X) δ γ = {!   !}
unquoteExp (cumu₀ e) δ γ = {!   !}
unquoteExp (cumu₁ e) δ γ = {!   !}

reify : ∀{n Δ Γ T} → (δ : unquoteTCtx Δ)
  → unquoteCtx Γ δ → unquoteT T δ → Exp {n} Δ Γ T
reify {_} {_} {_} {Var₀ x} δ γ t = {!   !}
reify {_} {_} {_} {Var₁ x} δ γ t = {!   !}
reify {_} {_} {_} {Var₂ x} δ γ t = {!   !}
reify {_} {_} {_} {A ⇒ B} δ γ t
  = lambda (reify δ {!   !} {!   !})
reify {_} {_} {_} {⋁₀ T} δ γ t = {!   !}
reify {_} {_} {_} {⋁₁ T} δ γ t = {!   !}
reify {_} {_} {_} {cumu₀ T} δ γ t = {!   !}
reify {_} {_} {_} {cumu₁ T} δ γ t = {!   !}
{-

The idea in this file is to use NbE. But type are agda types.
So, if idₙ : ⋁ₙ X . cumu (X ⇒ X), then
normalize id₁ id₀ by
(unquote id₁) : (X : Set₀) → X → X

(unquote id₁) (Nf ∅ (⋁₀ X . X ⇒ X)) id₀

So, essentially define unquote and reify.
In order to do this, will need 2 or 3 hardcoded type levels, because
Agda can't handle arbitrary levels.

-}

  -- e.g. ⋁₀ . X . (cumu X) ⇒ (cumu X), should turn into
  -- (X : Type 0) → (Exp X) → (Exp X)
  -- (X : Set) → X → X
