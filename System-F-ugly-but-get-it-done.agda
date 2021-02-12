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
open import Data.List

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

renType : ∀{n Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
renType ren (Var x) = Var (ren x)
renType ren (A ⇒ B) = renType ren A ⇒ renType ren B
renType ren (⋁ T) = ⋁ (renType (liftTRen ren) T)
renType ren (cumu T) = cumu (renType ren T)

-- Do I need weakenLevel, weakenΔ, and weakenΓ ????
-- weaken : ∀{l} →

data Ctx : TCtx → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{n Δ} → Ctx Δ → Type n Δ → Ctx Δ

renΓ : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renΓ ren ∅ = ∅
renΓ ren (Γ , T) = renΓ ren Γ , renType ren T


data InCtx : ∀{n Δ} → (Γ : Ctx Δ) → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ Γ A} → {T : Type m Δ}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A
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

subCtx : ∀{n Δ Γ T} → (icx : InCtx {n} {Δ} Γ T) → Ctx Δ
subCtx (same {_} {_} {Γ}) =  Γ
subCtx (next {_} {_} {_} {_} {_} {T} icx) = subCtx icx , T

data Pre : ∀{Δ} → Ctx Δ → Set where
  same : ∀{Δ Γ} → Pre {Δ} Γ
  next : ∀{Δ Γ n} → {T : Type n Δ} → Pre {Δ} Γ → Pre (Γ , T)

data SameTypes : ∀{nA nB Δ} → Type nA Δ → Type nB Δ → Set where
  refl : ∀{n Δ} → {T : Type n Δ} → SameTypes T T

-- nothing means use toSub, just means just adjust x for new context.
varSub : ∀{Δ Γ n m A B} → (icx : InCtx {n} {Δ} Γ A)
  → (x : InCtx {m} Γ B) → (SameTypes B A) ⊎ (InCtx (subCtx icx) B)
varSub same same = inj₁ refl
varSub same (next x) = inj₂ x
varSub (next icx) same = inj₂ same
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ x' = inj₂ (next x')

-- https://readthedocs.org/projects/agda/downloads/pdf/latest/ page 166
case_of_ : ∀ {a b} → {A : Set a} → {B : Set b} → A → (A → B) → B
case x of f = f x

test : Dec ℕ
test = Relation.Nullary.yes 5

data TSubn : ℕ → TCtx → TCtx → Set where
  ∅ : ∀{n} → TSubn n ∅ ∅
  nextn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
  nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , m) (Δ₂ , m)

-- weaken1Sub : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n Δ₁ (Δ₂ , l)
-- weaken1Sub ∅ = ∅
-- weaken1Sub (nextn sub T) = nextn (weaken1Sub sub) (renType weaken1Δ T) -- TODO: maybe ren needs to be written differently now?
-- weaken1Sub (nextm sub x) = nextm (weaken1Sub sub) (next x)

liftTSubn : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , l) (Δ₂ , l)
liftTSubn = nextm

-- TODO: delete this
append1subn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
append1subn = nextn

idSubn : ∀{n Δ} → TSubn n Δ Δ
idSubn {n} {∅} = ∅
idSubn {n} {Δ , x} = nextm idSubn

applySub : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → InTCtx Δ₁ m → Type m Δ₂
applySub ∅ x = Var x
applySub (nextn sub T) same = T
applySub (nextn sub T) (next x) = applySub sub x
applySub (nextm sub) same = Var same
applySub (nextm sub) (next x) = renType weaken1Δ (applySub sub x)

subTypen : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
subTypen sub (Var x) = applySub sub x
subTypen sub (A ⇒ B) = subTypen sub A ⇒ subTypen sub B
subTypen sub (⋁ T)
  = ⋁ (subTypen (liftTSubn sub) T)
subTypen sub (cumu T) = cumu (subTypen sub T)

subΓn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subΓn sub ∅ = ∅
subΓn sub (Γ , T) = subΓn sub Γ , subTypen sub T

data Exp : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
  var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{n Δ Γ A B} → Exp {n} Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Tlambda : ∀{Δ n Γ T}
    → Exp (Δ , n) (renΓ weaken1Δ Γ) T → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subTypen (append1subn idSubn X) T)
  cumu : ∀{Δ n T Γ}
    → Exp {n} Δ Γ T
    → Exp {suc n} Δ Γ (cumu T)


mutual
  data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) (renΓ weaken1Δ Γ) T → Nf Δ Γ (⋁ T)
    -- ne : ∀{n Δ Γ T} → Ne {n} Δ Γ T → Nf Δ Γ T
    cumu : ∀{Δ n T Γ}
      → Nf {n} Δ Γ T
      → Nf {suc n} Δ Γ (cumu T)
    ne : ∀{n Δ Γ T nOut TOut}
      → (x : InCtx {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Δ Γ TOut

--                              T         ↓ outputN    ↓ output type
  data Args : ∀{n Δ} → Ctx Δ → Type n Δ → (nOut : ℕ) → Type nOut Δ  → Set where
    none : ∀{n Δ Γ T} → Args {n} {Δ} Γ T n T
    one : ∀{n Δ Γ A B nOut TOut} → Args Γ B nOut TOut
      → Nf Δ Γ A
      → Args {n} {Δ} Γ (A ⇒ B) nOut TOut
    One : ∀{n Δ Γ nOut TOut} → {T : Type (suc n) (Δ , n)} → (X : Type n Δ)
      → Args {suc n} {Δ} Γ (subTypen (append1subn idSubn X) T) nOut TOut
      → Args {suc n} {Δ} Γ (⋁ T) nOut TOut

    cumu : ∀{n Δ Γ T nOut TOut}
      → Args {n} {Δ} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut

joinArgs : ∀{n Δ Γ A m B l C}
  → Args {n} {Δ} Γ A m B → Args Γ B l C → Args Γ A _ C
joinArgs none args₂ = args₂
joinArgs (one args₁ e) args₂ = one (joinArgs args₁ args₂) e
joinArgs (One X args₁) args₂ = One X (joinArgs args₁ args₂)
joinArgs (cumu args₁) args₂ = cumu (joinArgs args₁ args₂)

idSubnApplyFact : ∀{n m Δ x} → Var x ≡ applySub {n} {m} (idSubn {n} {Δ}) x
idSubnApplyFact {_} {_} {_} {same} = refl
idSubnApplyFact {_} {_} {_} {next x} = cong (renType weaken1Δ) idSubnApplyFact

idSubnFact : ∀{n m Δ T} → T ≡ subTypen {n} {m} {Δ} {Δ} idSubn T
idSubnFact {_} {_} {_} {Var x} = idSubnApplyFact
idSubnFact {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ idSubnFact idSubnFact
idSubnFact {_} {_} {_} {⋁ T} = cong ⋁ idSubnFact -- NOTE: the implementation of TSub is key here, as liftTSub idSub = idSub DEFINITIONALLY
idSubnFact {_} {_} {_} {cumu T} = cong cumu idSubnFact

idSubnΓFact : ∀{n Δ Γ} → Γ ≡ subΓn {n} {Δ} idSubn Γ
idSubnΓFact {_} {_} {∅} = refl
idSubnΓFact {_} {_} {Γ , T} = cong₂ _,_ idSubnΓFact idSubnFact

-- subTypecomm : ∀{n m k Δ₁ Δ₂} → (T : Type k Δ₁) → (sub : TSubn n Δ₁ Δ₂)
--   → (renType (weaken1Δ {_} {m}) (subTypen sub T))
--     ≡ (subTypen (liftTSubn sub) (renType weaken1Δ T))
-- subTypecomm (Var x) sub = refl
-- subTypecomm (A ⇒ B) sub = cong₂ _⇒_ (subTypecomm A sub) (subTypecomm B sub)
-- subTypecomm (⋁ T) sub = cong ⋁ {!   !}
-- subTypecomm (cumu T) sub = {!   !}

-- define liftManyRen liftManySub, which takes List ℕ, and lifts a weaken or sub by all of those.
appendMany : TCtx → List ℕ → TCtx
appendMany Δ [] = Δ
-- appendMany Δ (n ∷ l) = appendMany (Δ , n) l
appendMany Δ (n ∷ l) = (appendMany Δ l) , n

liftManyRen : ∀{Δ₁ Δ₂} → (l : List ℕ) → TRen Δ₁ Δ₂ → TRen (appendMany Δ₁ l) (appendMany Δ₂ l)
liftManyRen [] ren = ren
-- liftManyRen (x ∷ l) ren = liftManyRen l (liftTRen ren)
liftManyRen (x ∷ l) ren = liftTRen (liftManyRen l ren)

liftManySub : ∀{Δ₁ Δ₂ n} → (l : List ℕ) → TSubn n Δ₁ Δ₂ → TSubn n (appendMany Δ₁ l) (appendMany Δ₂ l)
liftManySub [] sub = sub
-- liftManySub (x ∷ l) sub = liftManySub l (liftTSubn sub)
liftManySub (x ∷ l) sub = liftTSubn (liftManySub l sub)

subICXcomm : ∀{n m k Δ₁ Δ₂} → (l : List ℕ) → (x : InTCtx (appendMany Δ₁ l) k)
  → (sub : TSubn n Δ₁ Δ₂)
  →
    applySub (liftManySub l (liftTSubn sub)) (liftManyRen l weaken1Δ x)
    ≡ renType (liftManyRen l (weaken1Δ {_} {m})) (applySub (liftManySub l sub) x)
subICXcomm l x ∅ = {! l  !}
subICXcomm l x (nextn sub T) = {! x  !}
subICXcomm l x (nextm sub) = {!   !}

subTypecomm : ∀{n m k Δ₁ Δ₂} → (l : List ℕ) → (T : Type k (appendMany Δ₁ l)) → (sub : TSubn n Δ₁ Δ₂)
  →
    (subTypen (liftManySub l (liftTSubn sub)) (renType (liftManyRen l weaken1Δ) T ))
    ≡ (renType (liftManyRen l (weaken1Δ {_} {m})) (subTypen (liftManySub l sub) T ))
    -- ≡ (subTypen (liftTSubn (liftManySub l sub)) (renType (liftManyRen l weaken1Δ) T))
subTypecomm l (Var x) sub = subICXcomm l x sub
subTypecomm l (A ⇒ B) sub = cong₂ _⇒_ (subTypecomm l A sub) (subTypecomm l B sub)
subTypecomm l (⋁ T) sub = cong ⋁ (subTypecomm (_ ∷ l) T sub )
subTypecomm l (cumu T) sub = cong cumu (subTypecomm l T sub)

subΓcomm : ∀{n m Δ₁ Δ₂} → (Γ : Ctx Δ₁) → (sub : TSubn n Δ₁ Δ₂)
  →
    (subΓn (liftTSubn sub) (renΓ weaken1Δ Γ))
    ≡ (renΓ (weaken1Δ {_} {m}) (subΓn sub Γ))
subΓcomm ∅ sub = refl
subΓcomm (Γ , T) sub = cong₂ _,_ (subΓcomm Γ sub) (subTypecomm [] T sub)

liftCommType : ∀{Δ₁ Δ₂ n m} → (l : List ℕ) → {ren : TRen Δ₁ Δ₂}
  → (T : Type m (appendMany Δ₁ l))
  → renType (liftManyRen l (liftTRen {_} {_} {n} ren)) (renType (liftManyRen l weaken1Δ) T)
    ≡ renType (liftManyRen l weaken1Δ) (renType (liftManyRen l ren) T)
liftCommType l (Var x) = cong Var {!   !}
liftCommType l (A ⇒ B) = cong₂ _⇒_ (liftCommType l A) (liftCommType l B)
liftCommType l (⋁ T) = cong ⋁ (liftCommType (_ ∷ l) T)
liftCommType l (cumu T) = cong cumu (liftCommType l T)

liftCommΓ : ∀{Δ₁ Δ₂ n} → {ren : TRen Δ₁ Δ₂} → (Γ : Ctx Δ₁)
  → (renΓ ((liftTRen {_} {_} {n}) ren) (renΓ weaken1Δ Γ))
    ≡ renΓ weaken1Δ (renΓ ren Γ)
liftCommΓ ∅ = refl
liftCommΓ (Γ , T) = cong₂ _,_ (liftCommΓ Γ) (liftCommType [] T)

renICX : ∀{n Δ₁ Δ₂ Γ T} → (ren : TRen Δ₁ Δ₂)
  → InCtx {n} {Δ₁} Γ T → InCtx (renΓ ren Γ) (renType ren T)
renICX ren same = same
renICX ren (next x) = next (renICX ren x)
-- TODO: Do I need this? (and therefore liftCommType and liftCommΓ as well?)
renNf : ∀{n Δ₁ Δ₂ Γ T} → (ren : TRen Δ₁ Δ₂)
  → Nf {n} Δ₁ Γ T → Nf Δ₂ (renΓ ren Γ) (renType ren T)
renNf ren (lambda e) = lambda (renNf ren e)
renNf ren (Tlambda e) = Tlambda (subst (λ Γ → Nf _ Γ _) (liftCommΓ _) (renNf (liftTRen ren) e))
renNf ren (cumu e) = cumu (renNf ren e)
renNf ren (ne x args) = {!   !}

subRenCancelType : ∀{Δ n m} → (l : List ℕ) → {X : Type n Δ} → (T : Type m (appendMany Δ l))
  → subTypen (liftManySub l (append1subn idSubn X))
      (renType (liftManyRen l weaken1Δ) T)
    ≡ T
subRenCancelType l (Var x) = {!   !}
subRenCancelType l (A ⇒ B) = cong₂ _⇒_ (subRenCancelType l A) (subRenCancelType l B)
subRenCancelType l (⋁ T) = cong ⋁ (subRenCancelType (_ ∷ l) T)
subRenCancelType l (cumu T) = cong cumu (subRenCancelType l T)

subRenCancelΓ : ∀{Δ n} → {X : Type n Δ} → (Γ : Ctx Δ)
  → (subΓn (append1subn idSubn X) (renΓ weaken1Δ Γ))
    ≡ Γ
subRenCancelΓ ∅ = refl
subRenCancelΓ (Γ , T) = cong₂ _,_ (subRenCancelΓ Γ) (subRenCancelType [] T)

  -- → (subTypen (append1subn idSubn X) (applySub (liftTSubn sub) x))
    -- ≡ (applySub (append1subn sub X) x)
bigLemmaApply : ∀{Δ Δ' n m} → (l : List ℕ) → (sub : TSubn n Δ' Δ)
  → (x : InTCtx (appendMany (Δ' , n) l) m) → {X : Type n Δ}
  → (subTypen (liftManySub l (append1subn idSubn X)) (applySub (liftManySub l (liftTSubn sub)) x))
    ≡ (applySub (liftManySub l (append1subn sub X)) x)
bigLemmaApply [] ∅ same = refl
bigLemmaApply (x₁ ∷ l) ∅ same = refl
bigLemmaApply (x₁ ∷ l) ∅ (next x) = {!   !}
bigLemmaApply l (nextn sub x₁) x = {! x  !}
bigLemmaApply l (nextm sub) x = {! x  !}

  -- → (subTypen (append1subn idSubn X) (subTypen (liftTSubn sub) T))
    -- ≡ (subTypen (append1subn sub X) T)
bigLemma : ∀{Δ Δ' n m} → {sub : TSubn n Δ' Δ} → (l : List ℕ)
  → (T : Type m (appendMany (Δ' , n) l)) → {X : Type n Δ}
  → (subTypen (liftManySub l (append1subn idSubn X)) (subTypen (liftManySub l (liftTSubn sub)) T))
    ≡ (subTypen (liftManySub l (append1subn sub X)) T)
bigLemma l (Var x) = bigLemmaApply l _ x
bigLemma l (A ⇒ B) = cong₂ _⇒_ (bigLemma l A) (bigLemma l B)
bigLemma l (⋁ T) = cong ⋁ (bigLemma (_ ∷ l) T)
bigLemma l (cumu T) = cong cumu (bigLemma l T)

bigLemma' : ∀{Δ Δ' n m} → {sub : TSubn n Δ' Δ}
  → (T : Type m (Δ' , n)) → {X : Type n Δ}
  → (subTypen (append1subn idSubn X) (subTypen (liftTSubn sub) T))
    ≡ (subTypen (append1subn sub X) T)
bigLemma' (Var x) = {!   !}
bigLemma' (A ⇒ B) = cong₂ _⇒_ (bigLemma' A) (bigLemma' B)
bigLemma' (⋁ T) = cong ⋁ {! bigLemma' T  !}
bigLemma' (cumu T) = cong cumu (bigLemma' T)

subICXTSubn : ∀{n m Δ₁ Δ₂ Γ T} → (sub : TSubn n Δ₁ Δ₂)
  → InCtx {m} {Δ₁} Γ T
  → InCtx {m} (subΓn sub Γ) (subTypen sub T)
subICXTSubn sub same = same
subICXTSubn sub (next x) = next (subICXTSubn sub x)

mutual
  subNfTSubn : ∀{n m Δ₁ Δ₂ Γ T} → (sub : TSubn n Δ₁ Δ₂) → Nf {m} Δ₁ Γ T
    → Nf {m} Δ₂ (subΓn sub Γ) (subTypen sub T)
  subNfTSubn sub (lambda e) = lambda (subNfTSubn sub e)
  subNfTSubn {_} {_} {_} {_} {Γ} sub (Tlambda e)
    = Tlambda (subst (λ Γ → Nf _ Γ _ ) (subΓcomm Γ sub) (subNfTSubn (liftTSubn sub) e))
    -- = Tlambda {! subNfTSubn (liftTSubn sub) e  !} -- note that only Γ is a problem.
  subNfTSubn sub (cumu e) = cumu (subNfTSubn sub e)
  subNfTSubn sub (ne x args) = ne (subICXTSubn sub x) (subArgsTSubn sub args)

  subArgsTSubn : ∀{n m Δ₁ Δ₂ Γ T nOut TOut} → (sub : TSubn n Δ₁ Δ₂)
    → Args {m} {Δ₁} Γ T nOut TOut
    → Args (subΓn sub Γ) (subTypen sub T) nOut (subTypen sub TOut)
  subArgsTSubn sub none = none
  subArgsTSubn sub (one args e) = one (subArgsTSubn sub args) (subNfTSubn sub e)
  subArgsTSubn {_} {_} {_} {_} {_} {⋁ T} sub (One X args)
    = One (subTypen sub X) (subst (λ T → Args _ T _ _)
      {! trans ? (sym (bigLemma {_} {_} {_} {_} {_} [] T {X})) !} (subArgsTSubn sub args))
    -- I think this is two successive applications of bigLemma?
    -- = One (subTypen sub X) (subArgsTSubn {!   !} ?)
    -- = {!   !}
  subArgsTSubn sub (cumu args) = cumu (subArgsTSubn sub args)

mutual
  subNf0 : ∀{n' Δ Γ T'} → (T : Type 0 Δ) → (x : InCtx Γ T)
    → (toSub : Nf {0} Δ (subCtx x) T)
    → Nf {n'} Δ Γ T' → Nf Δ (subCtx x) T'
  subNf0 T x toSub (lambda e) = lambda (subNf0 T (next x) {!  toSub !} e)
  subNf0 T x toSub (Tlambda e)
    -- = Tlambda (subNf0 (renType weaken1Δ T) (renICX weaken1Δ x) (renNf weaken1Δ toSub) e)
    = Tlambda {! (subNf0 (renType weaken1Δ T) ? (renNf weaken1Δ toSub) e)  !}
  subNf0 T x toSub (cumu e) = cumu (subNf0 T x toSub e)
  subNf0 T x toSub (ne y args) with varSub x y
  ... | inj₁ refl = appNf0 T toSub (subArgs0 T x toSub args)
  ... | inj₂ y' = ne y' (subArgs0 T x toSub args)

  subArgs0 : ∀{n' l Δ Γ T' T₁} → (T : Type 0 Δ) → (x : InCtx Γ T)
    → (toSub : Nf {0} Δ (subCtx x) T)
    → Args {l} {Δ} Γ T₁ n' T' → Args (subCtx x) T₁ n' T'
  subArgs0 T x toSub none = none
  subArgs0 T x toSub (one args e) = one (subArgs0 T x toSub args) (subNf0 T x toSub e)
  subArgs0 T x toSub (One X args) = One X (subArgs0 T x toSub args)
  subArgs0 T x toSub (cumu args) = cumu (subArgs0 T x toSub args)

  appNf0 : ∀{Δ  Γ nOut TOut} → (T : Type 0 Δ)
    → Nf {0} Δ Γ T
    → (count : Args Γ T nOut TOut)
    → Nf Δ Γ TOut
  appNf0 (A ⇒ B) (lambda e) (one args a)
    = appNf0 B (subNf0 A same a e) args
  appNf0 T (ne x args₁) args₂ = ne x (joinArgs args₁ args₂)
  appNf0 T e none = e

  appNfS : ∀{n Δ Δ' Γ nOut TOut} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → Nf {suc n} Δ Γ (subTypen sub T) -- Tsubbed
    → (args : Args Γ (subTypen sub T) nOut TOut) -- Tsubbed)
    → Nf Δ Γ TOut
    -- crucial idea: we are doing induction on T, not e.
  appNfS (Var X) sub e args = {!   !} -- really just have to prove sub X = X, so args = 0.
  appNfS (A ⇒ B) sub (lambda e) (one args a)
    = appNfS B sub {!   !} args
  appNfS (⋁ T) sub (Tlambda e) (One X args) = {!   !}
  appNfS (cumu T) sub (cumu e) (cumu args)
    = appNf (subTypen sub T) e args
  appNfS T sub (ne x args₁) args₂ = ne x (joinArgs args₁ args₂)
  appNfS T sub e none = e

  appNf : ∀{n Δ Γ nOut TOut} → (T : Type n Δ)
    → Nf {n} Δ Γ T
    → (args : Args Γ T nOut TOut)
    → Nf Δ Γ TOut
  appNf {zero} = appNf0
  appNf {suc n} {Δ} {Γ} {nOut} {TOut} T e args
    = appNfS T idSubn
      (subst (λ T → Nf _ _ T) idSubnFact e)
      (subst (λ T → Args Γ T nOut TOut) idSubnFact args)

-- data TSubn : ℕ → TCtx → TCtx → Set where
--   ∅ : ∀{n} → TSubn n ∅ ∅
--   nextn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
--   nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , m) (Δ₂ , m)

-- (sub ⊎ [X ↦ B])T
-- [X ↦ B]sub(T)

data 1TSub : ℕ → TCtx → TCtx → Set where

data TSubn2 : ℕ → TCtx → TCtx → Set where
  idSub2 : ∀{n Δ} → TSubn2 n Δ Δ
  cons : ∀{n Δ₁ Δ₂ Δ₃} → TSubn2 n Δ₁ Δ₂ → 1TSub n Δ₂ Δ₃ → TSubn2 n Δ₁ Δ₃

mutual
  subTypeHor : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
  subTypeHor ∅ T = {!   !}
  subTypeHor (nextn sub X) T = {! subTypeHor (nextm sub) T  !}
  subTypeHor (nextm sub) T = {!   !}

  subTypeVer : ∀{n m Δ₁ Δ₂} → TSubn2 n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
  subTypeVer idSub2 T = {!   !}

{-
-------------------------------------------------------------------------------
  "PAPER" PROOF:

  for all levels n, for all types T, (e : T)
  1) can be applied to any num of args
  2) can be substituted into any other expression

  If n = 0, then proof from S.T.L.C suffices, as no ∀ types.
  For all level n ≥ 1, for all typos (T , sub) where sub has vars at
  level (n-1) and for all e : sub(T), I will define
  (app e e₁ e₂ ... eₙ) for well types args, as well as
  e'[x ↦ e] for any well typed e'.

  The latter is easy, as it only depends on the former.

  For the former, cases on T:
  -- T = A ⇒ B. So, sub(T) = sub(A) ⇒ sub(B)
    then e = λ x . e' : sub(A) ⇒ sub(B)
    e₁ : sub(A). Recurse with (n, A, sub, e₁) to get e'[x ↦ e₁] : B.
    Next, recurse with (n, B, sub, e'[x ↦ e₁]) to apply rest of args.
  -- T = ∀ X . A.   So, sub(T) = ∀ X . sub(A)
    e : sub(T)
    then e = Λ X . e'  : ∀ X . sub(A)
    so e' : sub(A), so [X ↦ B]e : (sub ⊎ [X ↦ B])T       THIS JUDGEMENT HERE IS WHATS HARD
    definitionally, [X ↦ B]e : [X ↦ B](lift sub)(T)
    e₁ = B is a type.
    recurse on (n, A, sub ⊎ [X ↦ B] , [X ↦ B]e') to apply rest of args.
    NOTE: that A is at level (n-1), and so can only come up after a cumu.
    Therefore, X will be subbed for A by the time it comes up.
  -- T = X.  So sub(X) = X
    the can't be any well typed args. Keep in mind that X is at level n,
    and so sub(X) = X.
  -- T = cumu A. So, sub(cumu A) = cumu (sub(A))
    then e = cumu e'. Simply recurse with [n-1, sub(A), idSub, e']
    so need idSub(sub(A)) = sub(A)
-------------------------------------------------------------------------------

So, the takeaway is that it is crucial that sub be defined in a way so that
e.g. sub(A ⇒ B) = sub(A) ⇒ sub(B) is DEFINITIONALLY true.

We also need sub(X) = X, for X at level n+1 and sub at level n.

--------------------------------------------------------------------------------

-}

-- TODO FOR LATER:

{-
Then, try to fill in everything EXCEPT the commutivity proofs for InCtx cases.
-}
