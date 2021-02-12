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

mutual
  -- nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  -- nApp {_} {A ⇒ B} e = λ g → nApp (app e (reify g))
  -- nApp {_} {base} e = ne e

  -- reify : ∀{Γ} → {T : Exp Γ (λ _ → Set)} → (λ γ → unq γ T) → Exp Γ T
  reify : {Γ : Set₂} → {T : Exp Γ (λ _ → Γ → Set)}
    → ((γ : Γ) → (unq γ T) γ ) → Exp Γ λ γ → (unq γ T) γ
  reify {Γ} {T} = {! T  !}
  -- reify {_} {A ⇒ B} g
  --   = lambda (reify (λ ren → g (forget1ren ren) λ ren₂ → nApp (var (ren₂ (ren same)))))
  -- reify {_} {base} g = g idRen

-- Examples:

Bool = (X : Set) → X → X → X
Bool' : Exp ⊤ (λ _ → Set₁)
Bool' = Π₁ 𝓤₀ (Cumulativity (Π₀ EndCtx (Π₀ (Weaken EndCtx) (Weaken (Weaken EndCtx)))))

example1 : unq tt Bool' ≡ Bool
example1 = refl

true : Bool
true = λ X x₁ x₂ → x₁

true' : Exp ⊤ (λ _ → Bool)
true' = Lambda (Lambda (Lambda (Weaken EndCtx)))

example2 : unq tt true' ≡ true
example2 = refl
