open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)

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
    → Exp (Δ , n) (renΓ weaken1Δ Γ) T → Type n Δ → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subType (append1sub idSub X) T)

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

-- TSubn :
TSubn : ℕ → TCtx → TCtx → Set
TSubn (suc n) Δ₁ Δ₂ = InTCtx Δ₁ n → Type n Δ₂
TSubn zero Δ₁ Δ₂ = ⊤

append1subn : ∀{n Δ₁ Δ₂} → TSubn (suc n) Δ₁ Δ₂ → Type n Δ₂ → TSubn (suc n) (Δ₁ , n) Δ₂
append1subn sub T same = T
append1subn sub T (next x) = sub x

-- TODO: really want TSub to only contain types at level < n.
data ArgCount : ∀{n Δ Δ'} → Type n Δ → TSub Δ Δ' → Set where
  none : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → ArgCount {n} {Δ} {Δ'} T sub
  one : ∀{n Δ Δ' A B} → {sub : TSub Δ Δ'} → ArgCount B sub
    → ArgCount {n} {Δ} {Δ'} (A ⇒ B) sub
  One : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → (X : Type n Δ') -- should this really be in Δ'
    → ArgCount {_} {Δ , n} {Δ'} T (append1sub sub X)
    → ArgCount (⋁ T) sub -- (⋁ T) sub
  -- oneX : ∀{n Δ Δ' x sub} → ArgCount {!  sub x  !} {! idSub  !} → ArgCount {suc n} {Δ} {Δ'} (Var x) sub
  cumu : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'}
    → ArgCount {n} (subType sub T) idSub → ArgCount T sub

-- TODO: TODO: can we just let Δ' = Δ
-- No. Δ' is the original Δ

mutual
  -- partially unquoted Exp
  PUExp : ∀{n Δ Δ'} → {T : Type n Δ} → (sub : TSub Δ Δ')
    → ArgCount T sub → Ctx Δ → Set
  PUExp {n} {Δ} sub (none {_} {_} {_} {T}) Γ = Exp Δ Γ T -- TODO: should be Nf
  PUExp sub (one {_} {_} {_} {A} count) Γ = {-(GExp Γ A)-} ⊤ → PUExp sub count Γ
  PUExp sub (One X count) Γ
    = PUExp (append1sub sub X) count (renΓ weaken1Δ Γ) -- PUExp {! count  !} {! Γ  !}
  PUExp {_} {Δ} {Δ'} sub (cumu count) Γ = PUExp idSub count (subΓ sub Γ)

  -- Exp that can be partially unquoted to any amount
  APUExp : ∀{n Δ Δ'} → Ctx Δ → TSub Δ Δ' → Type n Δ → Set
  APUExp Γ sub T = (count : ArgCount T sub) → PUExp sub count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExp : ∀{n Δ Δ'} → Ctx Δ → TSub Δ Δ' → Type n Δ → Set
  GExp Γ sub T = ∀{Γ'} → Ren Γ Γ' → APUExp Γ' sub T -- NOTE: the key was using Ren instead of Sub here!
{-
data ArgCount : ∀{n Δ} → Type n Δ → Set where
  none : ∀{n Δ T} → ArgCount {n} {Δ} T
  one : ∀{n Δ A B} → ArgCount B → ArgCount {n} {Δ} (A ⇒ B)
  One : ∀{n m Δ T} → (X : Type m Δ) -- The fact that this arg is here and not in PUExp reflects that in System-F, types are present in source code and not calculated at runtime.
    → ArgCount {n} {Δ} (subType (append1sub idSub X) T) → ArgCount (⋁ T)
    -- TODO: using subType in ArgCount might not be the correct approach.
    -- Maybe instead it should keep track of type substitutions and
    -- whenever there is a case with count ≠ none, but T = X, then
    -- it will use a substitution?

mutual
  -- partially unquoted Exp
  PUExp : ∀{n Δ} → {T : Type n Δ} → ArgCount T → Ctx Δ → Set
  PUExp {n} {Δ} (none {_} {_} {T}) Γ = Exp Δ Γ T -- TODO: should be Nf
  PUExp (one {_} {_} {A} count) Γ = (GExp Γ A) → PUExp count Γ
  -- TODO:
  -- PUExp (one {_} {_} {A} count) Γ = (Exp Γ A → Set n) → PUExp count Γ
  -- TODO: try using girard's method here. On left, say any predicate at level n, instead of
  PUExp (One {_} {m} {Δ} {T} X count) Γ
    = PUExp {! count  !} {! Γ  !}
    -- PROBLEM: the output should really be in a type which incorporates
    -- X. In order to do this (and preserve termination), should incorporate a
    -- Sub into the type of PUExp I think?

  -- Exp that can be partially unquoted to any amount
  APUExp : ∀{n Δ} → Ctx Δ → Type n Δ → Set
  APUExp Γ T = (count : ArgCount T) → PUExp count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExp : ∀{n Δ} → Ctx Δ → Type n Δ → Set
  GExp Γ T = ∀{Γ'} → Ren Γ Γ' → APUExp Γ' T -- NOTE: the key was using Ren instead of Sub here!
-}
