{-# OPTIONS --rewriting #-}

open import Data.Nat
-- open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  n : ℕ
--  l : Set
--  j : l
--  noOnes : 1 ≡ 2


postulate
  f : ℕ → ℕ
  m : ℕ
  noOnes : ∀{x} → f x ≡ 2
  storage : Set
  inn : ℕ → storage
  out : storage → ℕ
  facc : ∀{n} → out (inn n) ≡ n

{-# REWRITE noOnes facc #-}

-- Self : (T : (Self T) → Set) → Set
-- self : {T : (Self T) → Set} → (e : T e) → Self T

-- postulate
  -- Self : SelfType

SelfT : Set
T' : SelfT → Set
postulate
  Self : (SelfT → Set) → Set
  T : Self T' → Set

-- -- variable


SelfT = Self T'
T' = T
--
-- postulate
--   rewrite1 : Self T' ≡ Self T
--
-- {-# REWRITE rewrite1 #-}

d : Self T → Set
d = T

-- So I have T : Self T → Set, and Self : Self T → Set.
-- The problem is that these are just postulated values, I need this for
-- variable T?

Te : Set
e' : Te
postulate
  e : T e'
  -- self : (e : T e') → Self T

Te = T e'
e' = e




-- SelfType = (T : SelfT T → Set) → Set
--   where
--         SelfT' : Set
--         SelfT : SelfT' → Set
--         SelfT T = {! Self T  !}
--         SelfT' = ?
--         boo = 8

-- data Ex : Ex ex where
--   ex : Ex ex

Exex : Set
Ex' : Exex → Set
ex' : Exex
data Ex : Exex → Set where
  ex : Ex ex'
Exex = Ex' ex'
Ex' = Ex
ex' = ex
postulate
  indEx : {P : {x : Ex ex} → Ex x → Set} → P ex → {x : Ex ex} → (xx : Ex x) → P xx
  indExRewrite : {P : {x : Ex ex} → Ex x → Set} → {Pex : P ex}
    → indEx {P} Pex ex ≡ Pex

{-# REWRITE indExRewrite #-}

exampleIndEx : ∀{x : Ex ex} → Ex x → ℕ
exampleIndEx = indEx 6

test1 : exampleIndEx ex ≡ 6
test1 = refl

q : ℕ
q = b
  where
  b : ℕ
  c : ℕ
  c = 8
  b = 7
