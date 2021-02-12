{-# OPTIONS --rewriting --cumulativity #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive

module JLevels where

maxL = lsuc (lsuc (lsuc (lsuc (lsuc (lsuc (lsuc (lsuc (lsuc (lsuc (lsuc lzero))))))))))

postulate
  Leveln : Level → Set maxL
  Setn : ∀{l} → Leveln l → Set maxL
  Setn≡ : ∀{l} → {i : Leveln l} → _≡_ {lsuc (maxL ⊔ (lsuc l))} {Set (maxL ⊔ (lsuc l))}
    (Setn i) (Set l)
  l0 : ∀{l} → Leveln l
  l1 : ∀{l} → Leveln l
  l2 : ∀{l} → Leveln l
  l3 : ∀{l} → Leveln l
  l4 : ∀{l} → Leveln l
  l5 : ∀{l} → Leveln l
  l0≡ : ∀{l} → Setn {l} l0 ≡ Set lzero
  l1≡ : ∀{l} → Setn {l} l1 ≡ Set (lsuc lzero)
  l2≡ : ∀{l} → Setn {l} l2 ≡ Set (lsuc (lsuc lzero))
  l3≡ : ∀{l} → Setn {l} l3 ≡ Set (lsuc (lsuc (lsuc lzero)))
  l4≡ : ∀{l} → Setn {l} l4 ≡ Set (lsuc (lsuc (lsuc (lsuc lzero))))
  l5≡ : ∀{l} → Setn {l} l5 ≡ Set (lsuc (lsuc (lsuc (lsuc (lsuc lzero)))))
  jsuc : ∀{l} → Leveln l → Leveln (lsuc l)
  jsuc0≡ : jsuc l0 ≡ l1
  jsuc1≡ : jsuc l1 ≡ l2
  jsuc2≡ : jsuc l2 ≡ l3
  jsuc3≡ : jsuc l3 ≡ l4
  jsuc4≡ : jsuc l4 ≡ l5
  jTol : ∀{l} → Leveln l → Level
  jTol0≡ : ∀{l} → jTol {l} l0 ≡ lzero
  jTol1≡ : ∀{l} → jTol {l} l1 ≡ (lsuc lzero)
  jTol2≡ : ∀{l} → jTol {l} l2 ≡ (lsuc (lsuc lzero))
  jTol3≡ : ∀{l} → jTol {l} l3 ≡ (lsuc (lsuc (lsuc lzero)))
  jTol4≡ : ∀{l} → jTol {l} l4 ≡ (lsuc (lsuc (lsuc (lsuc lzero))))
  jTol5≡ : ∀{l} → jTol {l} l5 ≡ (lsuc (lsuc (lsuc (lsuc (lsuc lzero)))))

{-# REWRITE Setn≡ l0≡ l1≡ l2≡ l3≡ l4≡ l5≡ jsuc0≡ jsuc1≡ jsuc2≡ jsuc3≡ jsuc4≡
    jTol0≡ jTol1≡ jTol2≡ jTol3≡ jTol4≡ jTol5≡ #-}

Level₀ = Leveln lzero
Level₁ = Leveln (lsuc lzero)
Level₂ = Leveln (lsuc (lsuc lzero))

test : (l : Level₁) → (Setn l) → Set₁
test l T = T

test2 : (l : Leveln (lsuc (lsuc (lsuc (lsuc lzero))))) → (Setn l) → Setn l
test2 l T = T
