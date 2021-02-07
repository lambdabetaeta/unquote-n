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

mutual
  data Context : Set where
    ∅ : Context
    consT : (Γ : Context) → ℕ → Context
    consE : ∀{n} → (Γ : Context) → Type n Γ → Context

  data InTCtx : ℕ → Context → Set where
    same : ∀{Γ n} → InTCtx n (consT Γ n)
    nextT : ∀{Γ n} → InTCtx n Γ → InTCtx n (consT Γ n)
    nextE : ∀{Γ n T} → InTCtx n Γ → InTCtx n (consE {n} Γ T)

  data Type : ℕ → Context → Set where
    Var : ∀{Γ n} → InTCtx n Γ → Type n Γ
    -- NOTE what I've done here, essentially make it dependent!!!
    _⇒_ : ∀{n Γ} → (A : Type n Γ) → (Type n (consE Γ A)) → Type n Γ
    ⋁ : ∀{n Γ} → Type (suc n) (consT Γ n) → Type (suc n) Γ
    cumu : ∀{n Γ} → Type n Γ → Type (suc n) Γ

  -- I COULD make type : Type, InCtx = InTCtx, lambda = TLambda, ...
  -- LETS DO IT!!!! WHY NOT!!!!!!!!!

  -- Remains to be seen if this is good design, but Γfull is the context in which
  -- we have a variable, while Γpre is the prefix of the context before that variable.
  data InCtx : ∀{n} → (Γfull Γpre : Context) → Type n Γpre → Set where
    same : ∀{Γ n T} → InCtx {n} (consE {n} Γ T) Γ T
    nextT : ∀{Γfull Γpre n A} → InCtx {n} Γfull Γpre A
      → InCtx {n} (consT Γfull n) Γpre A
    nextE : ∀{Γfull Γpre n T A} → InCtx {n} Γfull Γpre A
      → InCtx {n} (consE {n} Γfull T) Γpre A

  data Nf : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Nf {n} (consE Γ A) B → Nf {n} Γ (A ⇒ B)
    Tlambda : ∀{Γ n T} → Nf (consT Γ n) T → Nf Γ (⋁ T)
    cumu : ∀{Γ n T} → Nf {n} Γ T → Nf {suc n} Γ (cumu T)
    ne : ∀{n Γ T nOut TOut}
      → (x : InCtx {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Γ TOut

-- --                              T         ↓ outputN    ↓ output type
  data Args : ∀{n} → (Γ : Context) → Type n Γ → (nOut : ℕ) → Type nOut Γ  → Set where
--     none : ∀{n Δ Γ T} → Args {n} {Δ} Γ T n T
--     one : ∀{n Δ Γ A B nOut TOut} → Args Γ B nOut TOut
--       → Nf Δ Γ A
--       → Args {n} {Δ} Γ (A ⇒ B) nOut TOut
--     One : ∀{n Δ Γ nOut TOut} → {T : Type (suc n) (Δ , n)} → (X : Type n Δ)
--       → Args {suc n} {Δ} Γ (subTypen (append1subn idSubn X) T) nOut TOut
--       → Args {suc n} {Δ} Γ (⋁ T) nOut TOut
--
--     cumu : ∀{n Δ Γ T nOut TOut}
--       → Args {n} {Δ} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut
