open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)
open import Data.Sum

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

TRen : TCtx → TCtx → Set
TRen Δ₁ Δ₂ = ∀{n} → InTCtx Δ₁ n → InTCtx Δ₂ n

weaken1Δ : ∀{Δ n} → TRen Δ (Δ , n)
weaken1Δ ren = next ren

liftTRen : ∀{Δ₁ Δ₂ n} → TRen Δ₁ Δ₂ → TRen (Δ₁ , n) (Δ₂ , n)
liftTRen ren same = same
liftTRen ren (next itc) = next (ren itc)

-- represents a type at level l
data Type : ℕ → TCtx →  Set where
  Var : ∀{Δ n} → InTCtx Δ n → Type n Δ
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
  -- ⋁ : ∀{n m Δ} → Type m (Δ , n) → Type (m ⊔ (suc n)) Δ -- TODO: is this older version of ∀ more powerful in a meaningful way?
  ⋁ : ∀{n Δ} → Type (suc n) (Δ , n) → Type (suc n) Δ
  -- In order to be able to apply e.g. id₃ : (∀₃ X . X → X) like (id₃ (∀₀ X . X → X) id₁)
  -- need to be able to bring types up to a higher level
  cumu : ∀{n Δ} → Type n Δ → Type (suc n) Δ

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = ∀{n} → InTCtx Δ₁ n → Type n Δ₂

forget1TSub : ∀{Γ₁ Γ₂ T} → TSub (Γ₁ , T) Γ₂ → TSub Γ₁ Γ₂
forget1TSub sub x = sub (next x)

renType : ∀{n Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
renType ren (Var x) = Var (ren x)
renType ren (A ⇒ B) = renType ren A ⇒ renType ren B
renType ren (⋁ T) = ⋁ (renType (liftTRen ren) T)
renType ren (cumu T) = cumu (renType ren T)

liftTSub : ∀{Δ₁ Δ₂ n} → TSub Δ₁ Δ₂ → TSub (Δ₁ , n) (Δ₂ , n)
liftTSub sub same = Var same
liftTSub sub (next itc) = renType weaken1Δ (sub itc)

subType : ∀{n Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
subType sub (Var x) = sub x
subType sub (A ⇒ B) = subType sub A ⇒ subType sub B
subType sub (⋁ T) = ⋁ (subType (liftTSub sub) T)
subType sub (cumu T) = cumu (subType sub T)

idSub : ∀{Δ} → TSub Δ Δ
idSub x = Var x

append1sub : ∀{Δ₁ n Δ₂} → TSub Δ₁ Δ₂ → Type n Δ₂ → TSub (Δ₁ , n) Δ₂
append1sub sub T same = T
append1sub sub T (next x) = sub x

-- Do I need weakenLevel, weakenΔ, and weakenΓ ????
-- weaken : ∀{l} →

data Ctx : TCtx → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{n Δ} → Ctx Δ → Type n Δ → Ctx Δ

renΓ : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renΓ ren ∅ = ∅
renΓ ren (Γ , T) = renΓ ren Γ , renType ren T

subΓ : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subΓ sub ∅ = ∅
subΓ sub (Γ , T) = subΓ sub Γ , subType sub T


data InCtx : ∀{n Δ} → (Γ : Ctx Δ) → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ Γ A} → {T : Type m Δ}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A

data Exp : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
  var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{n Δ Γ A B} → Exp {n} Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Tlambda : ∀{Δ n Γ T}
    → Exp (Δ , n) (renΓ weaken1Δ Γ) T → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subType (append1sub idSub X) T)

    -- TODO: delete Ren, I don't think we need it
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

{-
Question: If types at level n can only have ∀s at level n-1,
does this reduce the expressiveness of the language at all?

∀₀ X . (∀₁ Y . Y) → X
-}

-- TODO: really want TSub to only contain types at level < n.
data ArgCount : ∀{n Δ Δ'} → Type n Δ → TSub Δ Δ' → Set where
  none : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → ArgCount {n} {Δ} {Δ'} T sub
  one : ∀{n Δ Δ' A B} → {sub : TSub Δ Δ'} → ArgCount B sub
    → ArgCount {n} {Δ} {Δ'} (A ⇒ B) sub
  One : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → (X : Type n Δ') -- TODO: should this really be in Δ'
    → ArgCount {_} {Δ , n} {Δ'} T (append1sub sub X)
    → ArgCount (⋁ T) sub
  cumu : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'}
    → ArgCount {n} (subType sub T) idSub → ArgCount {suc n} (cumu T) sub

output : ∀{n Δ Δ' T} → (sub : TSub Δ Δ') → ArgCount {n} T sub → Type n Δ'
output {_} {_} {_} {T} sub none = subType sub T
output sub (one count) = output sub count
output sub (One X count) = output (append1sub sub X) count
output sub (cumu count) = cumu (output idSub count)

-- TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO
-- QUESTION: can I define some kind of special induction which captures the
-- pattern of "Induction on types, but keep track of sub, and every time
--  that you hit a cumu case, use sub before recursing"
-- TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO: TODO

-- typeInd : ∀{n Δ} → (T : Type n Δ) → (P : ∀{n Δ} → Type n Δ → Set)
--   → (∀{n Δ A B} → P A → P B → P {n} {Δ} (A ⇒ B))
--   → (∀{} → P)
--   → P T
-- typeInd = {!   !}

-- -- This holds the args instead of just the count
-- data Args : ∀{n Δ Δ'} → Ctx Δ' → Type n Δ → TSub Δ Δ' → Set where
--   none : ∀{n Δ Δ' T Γ} → {sub : TSub Δ Δ'} → ArgCount {n} {Δ} {Δ'} T sub
--   one : ∀{n Δ Δ' A B} → {sub : TSub Δ Δ'} → ArgCount B sub
--     → -- This should be the only difference
--     → ArgCount {n} {Δ} {Δ'} (A ⇒ B) sub
--   One : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → (X : Type n Δ') -- TODO: should this really be in Δ'
--     → ArgCount {_} {Δ , n} {Δ'} T (append1sub sub X)
--     → ArgCount (⋁ T) sub
--   cumu : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'}
--     → ArgCount {n} (subType sub T) idSub → ArgCount {suc n} (cumu T) sub

mutual
  inputs : ∀{n Δ Δ' T} → (sub : TSub Δ Δ') → ArgCount {n} T sub → Ctx Δ' → Set
  inputs sub none Γ = ⊤
  inputs sub (one {_} {_} {_} {A} count) Γ = Nf _ Γ (subType sub A) × inputs sub count Γ
  inputs sub (One X count) Γ = inputs (append1sub sub X) count Γ
  inputs sub (cumu count) Γ = inputs idSub count Γ

  data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    ne : ∀{n Δ Γ T} → Ne {n} Δ Γ T → Nf {n} Δ Γ T
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) (renΓ weaken1Δ Γ) T → Nf Δ Γ (⋁ T)

  data Ne : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    -- var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Ne Δ Γ T
    -- app : ∀{n Δ Γ A B} → Ne {n} Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B
    TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
      → Ne Δ Γ (⋁ T) → (X : Type n Δ)
      → Ne Δ Γ (subType (append1sub idSub X) T)
    varapp : ∀{n Δ Γ} → {T : Type n Δ}
      → (count : ArgCount T idSub)
      → (icx : InCtx Γ T)
      → inputs idSub count Γ
      → Ne Δ Γ (output idSub count)

subCtx : ∀{n Δ Γ T} → (icx : InCtx {n} {Δ} Γ T) → Ctx Δ
subCtx (same {_} {_} {Γ}) =  Γ
subCtx (next {_} {_} {_} {_} {_} {T} icx) = subCtx icx , T

data Pre : ∀{Δ} → Ctx Δ → Set where
  same : ∀{Δ Γ} → Pre {Δ} Γ
  next : ∀{Δ Γ n} → {T : Type n Δ} → Pre {Δ} Γ → Pre (Γ , T)

weakenΓ : ∀{Δ n Γ} → Pre {Δ} Γ → Type n Δ → Ctx Δ
weakenΓ (same {_} {Γ}) A = Γ , A
weakenΓ (next {_} {Γ} {_} {T} pre) A = (weakenΓ pre A) , T

weakenICX : ∀{Δ n m Γ T} → (pre : Pre {Δ} Γ) → (W : Type n Δ)
  → (icx : InCtx {m} Γ T) → InCtx (weakenΓ pre W) T
weakenICX same W x = next x
weakenICX (next pre) W same = same
weakenICX (next pre) W (next x) = next (weakenICX pre W x)

-- nothing means use toSub, just means just adjust x for new context.
varSub : ∀{Δ Γ n A B} → (icx : InCtx {n} {Δ} Γ A)
  → (x : InCtx Γ B) → (B ≡ A) ⊎ (InCtx (subCtx icx) B)
varSub same same = inj₁ refl
varSub same (next x) = inj₂ x
varSub (next icx) same = inj₂ same
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ x' = inj₂ (next x')

weakenNf : ∀{n m Δ Γ T} → (pre : Pre Γ) → (W : Type n Δ)
  → Nf Δ Γ T → Nf {m} Δ (weakenΓ pre W) T

weakenInputs : ∀{n m Δ Δ' Γ T} → {sub : TSub Δ Δ'} → (pre : Pre Γ)
  → (W : Type n Δ')
  → (count : ArgCount {m} T sub)
  → inputs sub count Γ
  → inputs sub count (weakenΓ pre W)
weakenInputs pre W none inputs = tt
weakenInputs pre W (one count) (e , inputs)
  = weakenNf pre W e , weakenInputs pre W count inputs
weakenInputs pre W (One X count) inputs = weakenInputs pre W count inputs
weakenInputs pre W (cumu count) inputs = weakenInputs pre W count inputs

weakenNe : ∀{n m Δ Γ T} → (pre : Pre Γ) → (W : Type n Δ)
  → Ne Δ Γ T → Ne {m} Δ (weakenΓ pre W) T
weakenNe pre W (TApp e X) = TApp (weakenNe pre W e) X
weakenNe pre W (varapp count x inputs)
  = varapp count (weakenICX pre W x) (weakenInputs pre W count inputs)
weakenNf pre W (ne e) = ne (weakenNe pre W e)
weakenNf pre W (lambda v) = lambda (weakenNf (next pre) W v)
weakenNf pre W (Tlambda e) = Tlambda {! weakenNf ? ? e !}

weakenNf' : ∀{n m Δ Δ' Γ T} → {sub : TSub Δ Δ'} → (pre : Pre Γ)
  → (W : Type n Δ')
  → Nf Δ Γ T → Nf {m} Δ' {! weakenΓ pre ?  !}{-weakenΓ pre W-} (subType sub T)
weakenNf' = {!   !}
