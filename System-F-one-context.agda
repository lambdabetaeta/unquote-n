{-# OPTIONS --without-K #-}

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
    _,_ : ∀{n} → (Γ : Context) → Type n Γ → Context

  data Type : ℕ → Context → Set where
    Π : ∀{n Γ} → (A : Type n Γ) → (Type n (Γ , A)) → Type n Γ
    cumu : ∀{n Γ} → Type n Γ → Type (suc n) Γ
    type : ∀{Γ} → (n : ℕ) → Type (suc n) Γ
    Var : ∀{Γ n} → InCtx Γ (type n) → Type (suc n) Γ
    -- fromE : ∀{Γ n} → Nf Γ (type n) → Type n Γ -- If I ever use this, should be Nf, as even Exps need to use Nf's for types.

  data 1Weakening : Context → Context → Set where
    end : ∀{Γ n} → {T : Type n Γ} → 1Weakening Γ (Γ , T)
    next : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₁}
      → (wea : 1Weakening Γ₁ Γ₂)
      → 1Weakening (Γ₁ , T) (Γ₂ , 1weakenType wea T)

  data Weakening : Context → Context → Set where
    idWea : ∀{Γ} → Weakening Γ Γ
    _,_ : ∀{Γ₁ Γ₂ Γ₃} → Weakening Γ₁ Γ₂ → 1Weakening Γ₂ Γ₃ → Weakening Γ₁ Γ₃
    -- _,_ : ∀{Γ₁ Γ₂ Γ₃} → 1Weakening Γ₁ Γ₂ → Weakening Γ₂ Γ₃ → Weakening Γ₁ Γ₃

  data 1Sub : ∀{Γ₁ Γ₂} → 1Weakening Γ₂ Γ₁ → Set where
    end : ∀{Γ n} → {T : Type n Γ} → Exp Γ T → 1Sub (end {Γ} {n} {T})
    next : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₁}
      → {wea : 1Weakening Γ₁ Γ₂} → 1Sub wea
      → 1Sub (next {Γ₁} {Γ₂} {n} {T} wea)

  data InCtx : ∀{n} → (Γ : Context) → Type n Γ → Set where
    var : ∀{n Γpre T Γ} → (wea : Weakening (Γpre , T) Γ)
      → InCtx {n} Γ (weakenType wea (1weakenType end T))

  1weakenType : ∀{Γ₁ Γ₂ n} → 1Weakening Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  1weakenType wea (Π A B) = Π (1weakenType wea A) (1weakenType (next wea) B)
  1weakenType wea (cumu T) = cumu (1weakenType wea T)
  1weakenType wea (type n) = type n
  1weakenType wea (Var x) = Var (1weakenVar wea x)

  weakenType : ∀{Γ₁ Γ₂ n} → Weakening Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  weakenType idWea T = T
  weakenType (w , wea) T = 1weakenType wea (weakenType w T) -- weakenType wea (1weakenType w T)

  1weakenVar : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₁}
    → (wea : 1Weakening Γ₁ Γ₂)
    → InCtx Γ₁ T → InCtx Γ₂ (1weakenType wea T)
  1weakenVar wea (var wea₁) = var (wea₁ , wea)

  data Exp : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Exp {n} (Γ , A) B → Exp Γ (Π A B)
    cumu : ∀{Γ n T} → Exp {n} Γ T → Exp {suc n} Γ (cumu T)
    var : ∀{n Γ T} → InCtx {n} Γ T → Exp Γ T
    app : ∀{Γ n A B} → Exp {n} Γ (Π A B) → (a : Exp Γ A) → Exp {n} Γ {! subType a in B  !}
    fromT : ∀{Γ n} → Type n Γ → Exp Γ (type n)

  -- Normal form
  data Nf : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Nf {n} (Γ , A) B → Nf Γ (Π A B)
    cumu : ∀{Γ n T} → Nf {n} Γ T → Nf {suc n} Γ (cumu T)
    fromT : ∀{Γ n} → Type n Γ → Nf Γ (type n)
    -- Neutral form
    ne : ∀{n Γ T nOut TOut}
      → (x : InCtx {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Γ TOut

-- --                              T             ↓ outputN   ↓ output type
  data Args : ∀{n} → (Γ : Context) → Type n Γ → (nOut : ℕ) → Type nOut Γ
    → Set where
    none : ∀{n Γ T} → Args {n} Γ T n T
    one : ∀{n Γ A B nOut TOut}
      → (arg : Exp {n} Γ A)
      → Args Γ {! subType arg in B  !} nOut TOut
      → Args {n} Γ (Π A B) nOut TOut
    cumu : ∀{n Γ T nOut TOut}
      → Args {n} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut

  1subVar : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₁}
    → {wea : 1Weakening Γ₁ Γ₂}
    → 1Sub wea
    → InCtx Γ₂ (1weakenType wea T) → Exp Γ₁ T -- can't induct on x, so maybe subs can't be reverse of weakening here?
  1subVar sub x = {! x  !} -- If I don't have subs reverse of weakening, then will lambda case in appNf still work?
  -- Not to mention how can subs even work on this kind of variables that are weakenings?
  -- So definitely for the sake of argument just TRY standard subs, not reverse of weaks.

  -- BIG ISSUE: subNf needs to be parametrized by the type of the var that is being
  -- subbed. So, we need 1Sub, which substitutes exactly one thing of a given type!

  -- There is a big issue of how to resolve the need for indcution on input, with
  -- The need for subs to be reverse direction of weakening. It means that the input
  -- Is not something that can be matched on. Maybe, I can define first in terms of
  -- NOT reverse direction of weakening, then define that one in terms of it?

  -- Thinking about proof, we need 1Sub for e's so that subNf can be written mutual with
  -- appNf. But do we need TSubs separate from ESubs? In fact, if we have
  -- Tlambda and lambda combined, then it CANT be separate!!!!!!!
  -- PLAN FOR NOW: try with Tsub not separate, build 1wea, 1sub, wea, and sub
  -- If something doesn't work, then revise later!

  -- ISSUE : subNfE = 1Sub will need to be parametrized by TSub = Sub, but Sub is defined
  -- in terms of subNfE?
  -- Ya maybe thats actually fine?
  -- Like 1TSub could be separate, but doesn't actually accomplish anything?
