open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (suc ; Fin)
open import Data.Nat using (ℕ; _≟_; suc; zero)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Data.Sum
-- open import Relation.Negation
open import Data.Empty

-- TCtx l represents context of a type at level l,
-- which will only include type of up to level (l - 1)
-- because Fin n = {0 ,  ... , n-1}
data TCtx : Set where
  ∅ : TCtx
  _,_ : TCtx → ℕ → TCtx

-- TCtxCumu : ∀{l₁ l₂} → l₁ ≤ l₂ → TCtx l₁ → TCtx l₂
-- TCtxCumu z≤n Δ = {!   !}
-- TCtxCumu (s≤s p) Δ = {!   !}


data InTCtx : TCtx → ℕ → Set where
  same : ∀{Δ n} → InTCtx (Δ , n) n
  next : ∀{Δ n m} → InTCtx Δ n → InTCtx (Δ , m) n

-- represents a type at level l
data Type : ℕ → TCtx →  Set where
  Var : ∀{Δ n} → InTCtx Δ n → Type n Δ
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
  -- ⋁ : ∀{n m Δ} → Type m (Δ , n) → Type (m ⊔ (suc n)) Δ -- TODO: is this older version of ∀ more powerful in a meaningful way?
  ⋁ : ∀{n Δ} → Type (suc n) (Δ , n) → Type (suc n) Δ
  -- In order to be able to apply e.g. id₃ : (∀₃ X . X → X) like (id₃ (∀₀ X . X → X) id₁)
  -- need to be able to bring types up to a higher level
  cumu : ∀{n Δ} → Type n Δ → Type (suc n) Δ
data Ctx : TCtx → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{n Δ} → Ctx Δ → Type n Δ → Ctx Δ

data InCtx : ∀{n Δ} → (Γ : Ctx Δ) → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ Γ A} → {T : Type m Δ}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A
    -- TODO: delete Ren, I don't think we need it

data Weakening : ℕ → TCtx → TCtx → Set where
  ∅ : ∀{n} → Weakening n ∅ ∅
  same : ∀{n Δ₁ Δ₂ i} → Weakening n Δ₁ Δ₂ → Weakening n (Δ₁ , i) (Δ₂ , i)
  skip : ∀{n Δ₁ Δ₂} → Weakening n Δ₁ Δ₂ → Weakening n Δ₁ (Δ₂ , n)

weakenITC : ∀{Δ Δ' n m} → Weakening n Δ Δ'
  → InTCtx Δ m → InTCtx Δ' m
weakenITC (same wea) same = same
weakenITC (same wea) (next x) = next (weakenITC wea x)
weakenITC (skip wea) x = next (weakenITC wea x)

weakenType : ∀{Δ Δ' n m} → Weakening n Δ Δ'
  → Type m Δ → Type m Δ'
weakenType wea (Var x) = Var (weakenITC wea x)
weakenType wea (A ⇒ B) = weakenType wea A ⇒ weakenType wea B
weakenType wea (⋁ T) = ⋁ (weakenType (same wea) T)
weakenType wea (cumu T) = cumu (weakenType wea T)

weakenΓ : ∀{Δ Δ' n} → Weakening n Δ Δ'
  → Ctx Δ → Ctx Δ'
weakenΓ wea ∅ = ∅
weakenΓ wea (Γ , T) = weakenΓ wea Γ , weakenType wea T


data TSub3 : ∀{n Δ₁ Δ₂} → Weakening n Δ₂ Δ₁ → Set where
  ∅ : ∀{n} → TSub3 {n} ∅
  same : ∀{n Δ₁ Δ₂ i wea} → TSub3 {n} {Δ₁} {Δ₂} wea → TSub3 (same {_} {_} {_} {i} wea)
  skip : ∀{n Δ₁ Δ₂ wea} → TSub3 {n} {Δ₁} {Δ₂} wea
    → Type n Δ₂ → TSub3 (skip wea)

idWea : ∀{n Δ} → Weakening n Δ Δ
idWea {n} {∅} = ∅
idWea {n} {Δ , T} = same idWea

idSub3 : ∀{n Δ} → TSub3 {n} {Δ} idWea
idSub3 {n} {∅} = ∅
idSub3 {n} {Δ , T} = same idSub3

applySub3 : ∀{n m Δ₁ Δ₂} → (wea : Weakening n Δ₂ Δ₁) → TSub3 wea → InTCtx Δ₁ m → Type m Δ₂
applySub3 .(same _) (same sub) same = Var same
applySub3 .(same _) (same sub) (next x) = weakenType (skip idWea) (applySub3 _ sub x)
applySub3 {n} {m} {Δ₁} {Δ₂} .(skip _) (skip sub T) same = T
applySub3 .(skip _) (skip sub T) (next x) = applySub3 _ sub x

subType3 : ∀{n Δ Δ' m} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Type m Δ' → Type m Δ
subType3 wea sub (Var x) = applySub3 wea sub x
subType3 wea sub (A ⇒ B) = subType3 wea sub A ⇒ subType3 wea sub B
subType3 wea sub (⋁ T) = ⋁ (subType3 (same wea) (same sub) T)
subType3 wea sub (cumu T) = cumu (subType3 wea sub T)

mutual
  data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) (weakenΓ (skip idWea) Γ) T → Nf Δ Γ (⋁ T)
    cumu : ∀{Δ n T Γ}
      → Nf {n} Δ Γ T
      → Nf {suc n} Δ Γ (cumu T)
    ne : ∀{n Δ Γ T nOut TOut}
      → (x : InCtx {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Δ Γ TOut

--                              T         ↓ outputN    ↓ output type
  data Args : ∀{n Δ} → Ctx Δ → Type n Δ → (nOut : ℕ) → Type nOut Δ  → Set where
    none : ∀{n Δ Γ T} → Args {n} {Δ} Γ T n T
    one : ∀{n Δ Γ A B nOut TOut} → Args Γ B nOut TOut
      → Nf Δ Γ A
      → Args {n} {Δ} Γ (A ⇒ B) nOut TOut
    One : ∀{n Δ Γ nOut TOut} → {T : Type (suc n) (Δ , n)} → (X : Type n Δ)
      → Args {suc n} {Δ} Γ (subType3 (skip idWea) (skip idSub3 X) T) nOut TOut
      → Args {suc n} {Δ} Γ (⋁ T) nOut TOut

    cumu : ∀{n Δ Γ T nOut TOut}
      → Args {n} {Δ} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut

subΓ3 : ∀{n Δ Δ'} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Ctx Δ' → Ctx Δ
subΓ3 wea sub ∅ = ∅
subΓ3 wea sub (Γ , T) = subΓ3 wea sub Γ , subType3 wea sub T

lemma2 : ∀{Δ Δ' n m l} → {wea : Weakening n Δ Δ'} → {sub : TSub3 wea}
  → {T : Type m Δ'}
  → weakenType (skip {l} idWea) (subType3 wea sub T) ≡
      subType3 (same wea) (same sub) (weakenType (skip idWea) T)
lemma2 {_} {_} {_} {_} {_} {_} {_} {Var x} = {!   !}
lemma2 {_} {_} {_} {_} {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ lemma2 lemma2
lemma2 {_} {_} {_} {_} {_} {_} {_} {⋁ T} = cong ⋁ {! lemma2  !}
lemma2 {_} {_} {_} {_} {_} {_} {_} {cumu T} = {!   !}

lemma1 : ∀{Δ Δ' n m Γ} → {wea : Weakening n Δ Δ'} → {sub : TSub3 wea}
  → (weakenΓ (skip {m} idWea) (subΓ3 wea sub Γ))
    ≡ (subΓ3 (same wea) (same sub) (weakenΓ (skip idWea) Γ))
lemma1 {_} {_} {_} {_} {∅} = refl
lemma1 {_} {_} {_} {_} {Γ , T} = cong₂ _,_ lemma1 {!   !}

-- transSubWeaken : ∀{Δ₁ Δ₂ Δ₃ n} → {wea : Weakening n Δ₂ Δ₁} → TSub3 wea
--   → Weakening n Δ₁ Δ₂ → TSub3 n Δ₁ Δ₃
-- transSubWeaken sub wea = ?

subNf3 : ∀{n Δ Δ' m Γ T} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Nf Δ' Γ T
 → Nf {m} Δ (subΓ3 _ sub Γ) (subType3 _ sub T)
subNf3 wea sub (lambda e) = lambda (subNf3 _ sub e)
subNf3 wea sub (Tlambda e) = Tlambda {! subNf3 (same wea) (same sub) e  !} -- DOESNT seem like this is actually possible...
subNf3 wea sub (cumu e) = {!   !}
subNf3 wea sub (ne x args) = {!   !}

subNf3' : ∀{n Δ Δ' m Γ T} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Nf Δ' (weakenΓ wea Γ) (weakenType wea T)
 → Nf {m} Δ Γ T
subNf3' .∅ ∅ e = {! e  !}
subNf3' .(same _) (same sub) e = {! subNf3' sub e  !}
subNf3' .(skip _) (skip sub x) e = {!   !}

-- subNf3''' : ∀{n Δ Δ' m Γ} → (T : Type m (Δ' , n)) → (X : Type n Δ) → (wea : Weakening n Δ Δ')
--   → (sub : TSub3 wea)
--  → Nf (Δ , n) (weakenΓ (skip idWea) Γ) (subType3 (same wea) (same sub) T)
--  → Nf {m} Δ Γ (subType3 (skip wea) (skip sub X) T)
-- subNf3''' T X .∅ ∅ e = {! subNf3 ...   !} -- requires (weaken idWea)
-- subNf3''' T X .(same _) (same sub) e = {! weaken (subNf3''' _ sub e)  !}
-- subNf3''' T X .(skip _) (skip sub x) e = {!   !}
