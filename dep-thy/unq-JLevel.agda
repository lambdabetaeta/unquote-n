{-# OPTIONS --rewriting --cumulativity #-}

open import JLevels

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

-- maximum level used
m = lsuc (lsuc (lsuc (lsuc (lsuc lzero))))

------------------------------------------------------------
-- Representation of Dependent Type Theory in 30 lines
------------------------------------------------------------

mutual -- Γ ⊢ e : T    corresponds to     e : Exp Γ T
  data Exp : ∀{i : Leveln m} → (Γ : Setn i) → (T : Γ → Setn {m} i) → Setn {lsuc m} (jsuc i) where
    Lambda : ∀{i : Leveln m} → {Γ : Setn i} → {A : Γ → Setn i} → {B : Σ {jTol i} {jTol i} Γ A → Setn i} →
      Exp (Σ {jTol i} {jTol i} Γ A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    -- Π₀ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₀))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₀))
    --   → Exp Γ (λ γ → Set₀)
    -- Π₁ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₁))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₁))
    --   → Exp Γ (λ γ → Set₁)
    -- 𝓤₀ : {Γ : Set i} → Exp Γ (λ γ → Set₁)
    -- 𝓤₁ : {Γ : Set i} → Exp Γ (λ γ → Set₂)
    -- Cumulativity : ∀{Γ} → Exp Γ (λ _ → Set₀) → Exp Γ (λ _ → Set₁)
    -- App : {Γ : Set i} → {A : Γ → Set i} → {B : Σ Γ A → Set i} →
    --     Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    -- Weaken : {Γ : Set i} → {A B : Γ → Set i}
    --   → Exp Γ B → Exp (Σ Γ A) (λ γ → B (proj₁ γ))
    -- EndCtx : {Γ : Set i} → {A : Γ → Set i}
    --   → Exp (Σ Γ A) (λ γ → A (proj₁ γ))

  -- -- unquote
  -- unq : {Γ : Set i} → (γ : Γ) → {T : Γ → Set i} → Exp Γ T → T γ
  -- unq γ (Lambda e) = λ x → unq (γ , x) e
  -- unq γ (Weaken e) = unq (proj₁ γ) e
  -- unq γ (EndCtx) = proj₂ γ
  -- unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  -- unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  -- unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  -- unq γ 𝓤₀ = Set₀
  -- unq γ 𝓤₁ = Set₁
  -- unq γ (Cumulativity e) = unq γ e

-- Examples:

-- Bool = (X : Set) → X → X → X
-- Bool' : Exp ⊤ (λ _ → Set₁)
-- Bool' = Π₁ 𝓤₀ (Cumulativity (Π₀ EndCtx (Π₀ (Weaken EndCtx) (Weaken (Weaken EndCtx)))))
--
-- example1 : unq tt Bool' ≡ Bool
-- example1 = refl
--
-- true : Bool
-- true = λ X x₁ x₂ → x₁
--
-- true' : Exp ⊤ (λ _ → Bool)
-- true' = Lambda (Lambda (Lambda (Weaken EndCtx)))
--
-- example2 : unq tt true' ≡ true
-- example2 = refl
