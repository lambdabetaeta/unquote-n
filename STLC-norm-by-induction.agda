open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)
open import Data.List
open import Data.Unit
open import Data.Maybe

data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : Ctx → Type → Set where
  same : ∀{Γ T} → InCtx (Γ , T) T
  next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

subCtx : ∀{Γ T} → (icx : InCtx Γ T) → Ctx
subCtx (same {Γ}) =  Γ
subCtx (next {Γ} {T} icx) = subCtx icx , T

data Pre : Ctx → Set where
  same : ∀{Γ} → Pre Γ
  next : ∀{Γ T} → Pre Γ → Pre (Γ , T)

weakenΓ : ∀{Γ} → Pre Γ → Type → Ctx
weakenΓ (same {Γ}) A = Γ , A
weakenΓ (next {Γ} {T} pre) A = (weakenΓ pre A) , T

weakenICX : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → (icx : InCtx Γ T) → InCtx (weakenΓ pre W) T
weakenICX same W icx = next icx
weakenICX (next pre) W same = same
weakenICX (next pre) W (next icx) = next (weakenICX pre W icx)

-- -- nothing means use toSub, just means just adjust x for new context.
varSub : ∀{Γ A B} → (icx : InCtx Γ A)
  → (x : InCtx Γ B) → (B ≡ A) ⊎ (InCtx (subCtx icx) B)
varSub same same = inj₁ refl
varSub same (next x) = inj₂ x
varSub (next icx) same = inj₂ same
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ x' = inj₂ (next x')

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

output : ∀{T} → ArgCount T → Type
output (none {T}) = T
output (one count) = output count

mutual
  inputs : ∀{T} → ArgCount T → Ctx → Set
  inputs none Γ = ⊤
  inputs (one {A} count) Γ = Nf Γ A × inputs count Γ

  data Ne : Ctx → Type → Set where
    z : ∀{Γ} → Ne Γ Nat
    s : ∀{Γ} → Nf Γ Nat → Ne Γ Nat
    varapp : ∀{Γ T} → (count : ArgCount T)
      → (icx : InCtx Γ T)
      → inputs count Γ
      → Ne Γ (output count)

  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    fromU : ∀{Γ T} → Ne Γ T → Nf Γ T

weakenV : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → Nf Γ T → Nf (weakenΓ pre W) T

weakenInputs : ∀{Γ T} → (pre : Pre Γ) → (W : Type)
  → (count : ArgCount T)
  → inputs count Γ
  → inputs count (weakenΓ pre W)
weakenInputs pre W none inputs = tt
weakenInputs pre W (one count) (e , inputs)
  = weakenV pre W e , weakenInputs pre W count inputs

weakenV pre W (lambda v) = lambda (weakenV (next pre) W v)
weakenV pre W (fromU z) = fromU z
weakenV pre W (fromU (s x)) = fromU (s (weakenV pre W x))
weakenV pre W (fromU (varapp count x inputs))
  = fromU (varapp count (weakenICX pre W x) (weakenInputs pre W count inputs))

joinCounts : ∀{T} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
  → ArgCount T
joinCounts none count₂ = count₂
joinCounts (one count₁) count₂ = one (joinCounts count₁ count₂)

joinInputs : ∀{T Γ} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
  → inputs count₁ Γ → inputs count₂ Γ → inputs (joinCounts count₁ count₂) Γ
joinInputs none count₂ tt args₂ = args₂
joinInputs (one count₁) count₂ (e , args₁) args₂
  = e , joinInputs count₁ count₂ args₁ args₂

joinOutputs : ∀{T} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
  → output (joinCounts count₁ count₂) ≡ output count₂
joinOutputs none count₂ = refl
joinOutputs (one count₁) count₂ = joinOutputs count₁ count₂


mutual
  subv : ∀{Γ T} → ∀{T'} → (icx : InCtx Γ T)
    → (toSub : Nf (subCtx icx) T) → Nf Γ T' → Nf (subCtx icx) T'
  subv icx toSub (lambda v) = lambda (subv (next icx) (weakenV same _ toSub) v)
  subv icx toSub (fromU z) = fromU z
  subv icx toSub (fromU (s x)) = fromU (s (subv icx toSub x))
  subv icx toSub (fromU (varapp count x args)) with varSub icx x
  ... | inj₁ refl = appv toSub count (subInputs icx toSub count args)
  ... | inj₂ x' = fromU (varapp count x' (subInputs icx toSub count args))
  appv : ∀{Γ T} → (e : Nf Γ T)
    → (count : ArgCount T) → inputs count Γ → Nf Γ (output count)
  appv (lambda e) none tt = lambda e
  appv {_} {A ⇒ B} (lambda e) (one count) (a , inputs)
    = appv {_} {B} (subv {_} {A} same a e) count inputs
    --  Two recursions: one explicit, one through subv.
    -- Explicit:       count ↓  T ↑  inputs ↓  e ↑   e comes from e and inputs
    -- Through subv:   count ↑  T ↓  inputs ↑  e ↓   BUT count comes from e
    -- Maybe in sysF, we can let B be itself and not subbed,
    -- and then do the sub at the end?
    -- In order to apply something like (T = ∀ X . X → X) , e : T
    -- (e T e) would require TWO varapps, because the first would only see the
    -- arg type as X.
    -- But no, then this would break the whole mechanism by which this works!
    -- In order to try this, would first need to see if the "no varapp" version
    -- from the other file is viable with the subs from this file.
    -- TODO: think the system-F proof through on PAPER before trying anything.
  appv (fromU z) none tt = fromU z
  appv (fromU (s x)) none tt = fromU (s x)
  appv (fromU (varapp count₁ icx args₁)) count₂ args₂
    = fromU (subst (λ T → Ne _ T) (joinOutputs count₁ count₂)
        (varapp (joinCounts count₁ count₂) icx (joinInputs _ _ args₁ args₂)))

  subInputs : ∀{Γ T} → ∀{T'} → (icx : InCtx Γ T)
    → (toSub : Nf (subCtx icx) T) → (count : ArgCount T')
    → inputs count Γ → inputs count (subCtx icx)
  subInputs icx toSub none tt = tt
  subInputs icx toSub (one count) (e , inputs)
    = subv icx toSub e , subInputs icx toSub count inputs

id : Nf ∅ (Nat ⇒ Nat)
id = lambda (fromU (varapp none same tt ))

uno : Nf ∅ Nat
uno = fromU (s (fromU z))

idOne : Nf ∅ Nat
idOne = appv id (one none) (uno , tt)

test : idOne ≡ uno
test = refl
