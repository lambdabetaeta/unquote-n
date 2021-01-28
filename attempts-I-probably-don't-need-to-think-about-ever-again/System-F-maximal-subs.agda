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
mutual
  data Type : ℕ → TCtx →  Set where
    cumu : ∀{n Δ} → Type n Δ → Type (suc n) Δ
    st : ∀{n Δ} → SimpleType n Δ → Type n Δ
  data SimpleType : ℕ → TCtx →  Set where
    VarS : ∀{Δ n} → InTCtx Δ n → SimpleType n Δ
    _⇒S_ : ∀{n Δ} → Type n Δ → Type n Δ → SimpleType n Δ
    ⋁S : ∀{n Δ} → Type (suc n) (Δ , n) → SimpleType (suc n) Δ
    -- In order to be able to apply e.g. id₃ : (∀₃ X . X → X) like (id₃ (∀₀ X . X → X) id₁)
    -- need to be able to bring types up to a higher level
Var : ∀{Δ n} → InTCtx Δ n → Type n Δ
Var x = st (VarS x)
_⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
_⇒_ A B = st (A ⇒S B)
⋁ : ∀{n Δ} → Type (suc n) (Δ , n) → Type (suc n) Δ
⋁ T = st (⋁S T)

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = ∀{n} → InTCtx Δ₁ n → Type n Δ₂

forget1TSub : ∀{Γ₁ Γ₂ T} → TSub (Γ₁ , T) Γ₂ → TSub Γ₁ Γ₂
forget1TSub sub x = sub (next x)

renType : ∀{n Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
renType ren (st (VarS x)) = Var (ren x)
renType ren (st (A ⇒S B)) = renType ren A ⇒ renType ren B
renType ren (st (⋁S T)) = ⋁ (renType (liftTRen ren) T)
renType ren (cumu T) = cumu (renType ren T)

liftTSub : ∀{Δ₁ Δ₂ n} → TSub Δ₁ Δ₂ → TSub (Δ₁ , n) (Δ₂ , n)
liftTSub sub same = Var same
liftTSub sub (next itc) = renType weaken1Δ (sub itc)

subType : ∀{n Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
subType sub (st (VarS x)) = sub x
subType sub (st (A ⇒S B)) = subType sub A ⇒ subType sub B
subType sub (st (⋁S T)) = ⋁ (subType (liftTSub sub) T)
subType sub (cumu T) = cumu (subType sub T)

idTSub : ∀{Δ} → TSub Δ Δ
idTSub x = Var x

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
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ (st B)) → Exp Δ Γ A → Exp Δ Γ (st B)
  Tlambda : ∀{Δ n Γ T}
    → Exp (Δ , n) (renΓ weaken1Δ Γ) (st T) → Type n Δ → Exp Δ Γ (⋁ (st T))
  TApp : ∀{Δ Γ n} → {T : SimpleType (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ (st T))
    → (X : Type n Δ)
    → Exp Δ Γ (subType (append1sub idTSub X) (st T))

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
  one : ∀{n Δ Δ' A B} → {sub : TSub Δ Δ'} → ArgCount (st B) sub
    → ArgCount {n} {Δ} {Δ'} (A ⇒ (st B)) sub
  One : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'} → (X : Type n Δ') -- TODO: should this really be in Δ'
    → ArgCount {_} {Δ , n} {Δ'} (st T) (append1sub sub X)
    → ArgCount (⋁ (st T)) sub
  cumu : ∀{n Δ Δ' T} → {sub : TSub Δ Δ'}
    → ArgCount {n} (subType sub T) idTSub → ArgCount {suc n} (cumu T) sub

-- data InCtxS : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → (Γ : Ctx Δ)
--   → Type n Δ' → Set where
--   same : ∀{n Δ Δ' Γ} → {sub : TSub Δ' Δ} → {T : Type n Δ'}
--     → InCtxS {n} sub (Γ , subType sub T) T
--   -- next : ∀{n m Δ Γ A} → {sub : TSub Δ' Δ} → {T : Type m Δ}
--     -- → InCtxS {n} {Δ} Γ A → InCtxS (Γ , T) A

-- TODO: make CONTEXTS AND INCTX parametrized by sub!!!!! MAYBE???

--           THIS↓  THIS↓                    and THIS↓     make a Typo
data ExpS : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → Ctx Δ → Type n Δ' → Set where
  lambda : ∀{n Δ Δ' Γ A B} → {sub : TSub Δ' Δ}
    → ExpS {n} sub (Γ , subType sub A) B → ExpS sub Γ (A ⇒ B)
  Tlambda : ∀{Δ Δ' n Γ T} → {sub : TSub Δ' Δ} -- TODO: I got Tlambda case to typecheck, but is it correct?
    → ExpS {suc n} {Δ , n} {Δ' , n} (liftTSub sub) (renΓ weaken1Δ Γ) T
    → ExpS {suc n} {Δ} {Δ'} sub Γ (⋁ T)
  cumu : ∀{Δ Δ' n T Γ} → {sub : TSub Δ' Δ}
    → ExpS {n} {Δ} {Δ} idTSub Γ (subType sub T)
    → ExpS {suc n} {Δ} {Δ'} sub Γ (cumu T)
  var : ∀{n Δ Δ' Γ T} → {sub : TSub Δ' Δ}
    → InCtx {n} {Δ} Γ (subType sub (st T)) → ExpS {n} {Δ} {Δ'} sub Γ (st T)
  app : ∀{n Δ Δ' Γ A B} → {sub : TSub Δ' Δ}
    → ExpS {n} sub Γ (A ⇒ (st B)) → ExpS sub Γ A → ExpS sub Γ (st B)
  TApp : ∀{Δ Δ' Γ n} → {sub : TSub Δ' Δ}
    → {T : SimpleType (suc n) (Δ' , n)}
    → ExpS sub Γ (⋁ (st T))
    → (X : Type n Δ)
    → ExpS (append1sub sub X) Γ (st T)

expToExpS : ∀{n Δ Γ T} → Exp {n} Δ Γ T → ExpS {n} {Δ} {Δ} idTSub Γ T
expToExpS (var x) = {! var x  !}
-- As can be seen by this case, to convert will have to do at least some
-- sub computations...
expToExpS (lambda e) = lambda {! expToExpS e  !}
expToExpS (app e₁ e₂) = app {!   !} {!   !}
expToExpS (Tlambda e x) = Tlambda {!   !}
expToExpS (TApp e X) = {! TApp  !}

idType : Type 1 ∅
idType = ⋁ (cumu (Var same ⇒ Var same))

idExp : ExpS idTSub ∅ idType
idExp = Tlambda (cumu (lambda (var same)))

badExample : Type 1 ∅
badExample = ⋁ (cumu (Var same) ⇒ cumu (Var same))

-- badExExp : ExpS idTSub ∅ badExample
-- badExExp = Tlambda (lambda (var same))

mutual
  -- partially unquoted Exp
  --            ↓      ↓                  ↓
  PUExp : ∀{n Δ Δ'} → {T : Type n Δ'} → (sub : TSub Δ' Δ)
    → ArgCount T sub → Ctx Δ → Set
                                               -- TODO: should this really be in Δ' as opposed to Δ?
  PUExp {n} {Δ} {Δ'} sub (none {_} {_} {_} {T}) Γ
    -- = Exp Δ Γ (subType sub T) -- TODO: should be Nf
    = ExpS sub Γ T -- TODO: should be Nf
  PUExp {n} sub (one {_} {_} {_} {A} count) Γ
    = (GExpImpl {n} Γ sub A) → PUExp {n} sub count Γ
  PUExp {n} sub (One X count) Γ
    = PUExp {n} (append1sub sub X) count Γ
  PUExp {suc n} {Δ} {Δ'} sub (cumu count) Γ = PUExp idTSub count Γ -- NOTE: this step is what allows GExp to not be recursive: we only apply subs when decreasing level.
  -- TODO: think about if the above design of only applying subs at cumu case could be used to do inductive normalization of System-F, similar to how I do inductive normalization of STLC.

  -- Exp that can be partially unquoted to any amount
  APUExp : ∀{n Δ Δ'} → Ctx Δ → TSub Δ' Δ → Type n Δ' → Set
  APUExp {n} Γ sub T = (count : ArgCount T sub) → PUExp {n} sub count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExpImpl : ∀{n Δ Δ'} → Ctx Δ → TSub Δ' Δ → Type n Δ' → Set
  GExpImpl {n} Γ sub T = ∀{Γ'} → Ren Γ Γ' → APUExp {n} Γ' sub T

  -- GExp : ∀{n Δ} → Ctx Δ → Type n Δ → Set
  -- GExp Γ T = GExpImpl Γ idTSub T

Sub : ∀{Δ Δ'} → TSub Δ' Δ → Ctx Δ → Ctx Δ → Set
Sub {Δ} sub Γ₁ Γ₂ = ∀{n T} → InCtx {n} Γ₁ (subType sub T) → GExpImpl Γ₂ sub T

nApp : ∀{n Δ Δ' Γ T} → (sub : TSub Δ' Δ)
  → (count : ArgCount {n} T sub) → ExpS sub Γ T → PUExp sub count Γ
nApp sub none e = e
nApp sub (one count) e = λ x → nApp sub count (app e (x idRen none))
  -- The below hole previously needed  a proof about equality of some subs
  -- (append1sub idTSub X) ∘ (liftTSub sub) = append1sub sub X
  -- now that Exp is parametrized by sub, simple and easy
nApp sub (One X count) e = nApp (append1sub sub X) count (TApp e X)
  -- This needs a proof that
  -- idTSub ∘ sub ≡ sub
nApp sub (cumu count) (cumu e) = nApp idTSub count e

idSub : ∀{Δ Δ' Γ} → (tsub : TSub Δ' Δ) → Sub {Δ} tsub Γ Γ
idSub tsub x ren count = nApp tsub count {!  ExpS.var (ren x)  !}
-- idSub x ren count = nApp count (var (ren x))

-- liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
-- liftSub sub same ren count = nApp count (var (ren same))
-- liftSub sub (next itc) ren = sub itc (forget1ren ren)

-- _∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
-- s₁ ∘ s₂ = λ x → s₂ (s₁ x)
--
-- transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
-- transSR sub ren x ren₂ = sub x (ren ∘ ren₂)
--
-- append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → GExp Γ₂ A → Sub (Γ₁ , A) Γ₂
-- append1sub sub e same ren = e ren
-- append1sub sub e (next x) ren = sub x ren

{-
TODO: THE PLAN!

The is the maximum file, so I'm trying the design of having subs (typos)
in as many places as possible.
-}
