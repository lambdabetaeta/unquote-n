{-# OPTIONS --cumulativity --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

------------------------------------------------------------
-- Representation of Dependent Type Theory in 30 lines
------------------------------------------------------------

mutual -- Γ ⊢ e : T    corresponds to     e : Exp Γ T
  data Exp : (Γ : Set i) → (T : Γ → Set i) → Set j where
    Lambda : {Γ : Set i} → {A : Γ → Set i} → {B : Σ {i} {i} Γ A → Set i} →
      Exp (Σ {i} {i} Γ A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Π₀ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₀))
      → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    Π₁ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₁))
      → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₁))
      → Exp Γ (λ γ → Set₁)
    𝓤₀ : {Γ : Set i} → Exp Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Set i} → Exp Γ (λ γ → Set₂)
    Cumulativity : ∀{Γ} → Exp Γ (λ _ → Set₀) → Exp Γ (λ _ → Set₁)
    App : {Γ : Set i} → {A : Γ → Set i} → {B : Σ Γ A → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Weaken : {Γ : Set i} → {A B : Γ → Set i}
      → Exp Γ B → Exp (Σ Γ A) (λ γ → B (proj₁ γ))
    EndCtx : {Γ : Set i} → {A : Γ → Set i}
      → Exp (Σ Γ A) (λ γ → A (proj₁ γ))

  -- unquote
  unq : {Γ : Set i} → (γ : Γ) → {T : Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Weaken e) = unq (proj₁ γ) e
  unq γ (EndCtx) = proj₂ γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ (Cumulativity e) = unq γ e

data ArgCount : {Γ : Set i} → (Γ → Set i) → Set j where
  none : {Γ : Set i} → {T : Γ → Set i} → ArgCount T
  one : {Γ : Set i} → {A : Γ → Set i} → {B : Σ Γ A → Set i}
      → (x : Exp Γ A) → ArgCount (λ γ → B (γ , unq γ x))
      → ArgCount (λ γ → (a : A γ) → B (γ , a))

ToType : {Γ : Set i} → {T : Γ → Set i}
  → ArgCount T → Set j
ToType {Γ} {T} none = Exp Γ T
ToType (one {Γ} {A} x count)
  = ((count' : ArgCount A) → (ToType count')) → ToType count

{-

Termination check fails on the above. This tells us something very
important about why this method DID pass the termination check in STLC:
There, A was structurally less than the type (A ⇒ B).
The good news is that this also works for dependent function types.
The bad news is that they have to be represented as an inductive type,
and the "base types" method from this file doesn't work.

-}
