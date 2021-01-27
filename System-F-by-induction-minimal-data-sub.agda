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

-- nothing means use toSub, just means just adjust x for new context.
varSub : ∀{Δ Γ n A B} → (icx : InCtx {n} {Δ} Γ A)
  → (x : InCtx Γ B) → (B ≡ A) ⊎ (InCtx (subCtx icx) B)
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
  -- nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → InTCtx Δ₂ m → TSubn n (Δ₁ , m) Δ₂
  -- TODO: think later about old vs new design here. Which makes things more definitionally true?
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
applySub (nextm sub) (next x) = renType weaken1Δ (applySub sub x) -- TODO: again, maybe think about different impl of renaming

subTypen : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
subTypen sub (Var x) = applySub sub x
subTypen sub (A ⇒ B) = subTypen sub A ⇒ subTypen sub B
subTypen sub (⋁ T) = ⋁ (subTypen (liftTSubn sub) T)
subTypen sub (cumu T) = cumu (subTypen sub T)

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

-- IDEA: try making ArgCount parametrized by outputN and also output!!!

data ArgCount : ∀{n Δ} → Type n Δ → Set where
  none : ∀{n Δ T} → ArgCount {n} {Δ} T
  one : ∀{n Δ A B} → ArgCount B → ArgCount {n} {Δ} (A ⇒ B)
  One : ∀{n Δ T} → (X : Type n Δ)
    → ArgCount {_} {Δ , n} T → ArgCount (⋁ T)
  cumu : ∀{n Δ T}
    → ArgCount {n} {Δ} T → ArgCount {suc n} (cumu T)

outputN : ∀{n Δ T} → ArgCount {n} {Δ} T → ℕ
outputN {n} none = n
outputN (one count) = outputN count
outputN (One X count) = outputN count
outputN (cumu count) = outputN count

output : ∀{n Δ T} → (count : ArgCount {n} {Δ} T) → Type (outputN count) Δ
output (none {_} {_} {T}) = T
output (one count) = output count
-- TODO: might have to do sub with Pre here to fit with later?
output (One X count) = subTypen (append1subn idSubn X) (output count)
output (cumu count) = output count

mutual
  inputs : ∀{n Δ T} → ArgCount {n} {Δ} T → Ctx Δ → Set
  inputs none Γ = ⊤
  inputs (one {_} {_} {A} count) Γ = Nf _ Γ A × inputs count Γ
  -- TODO: again, might have issues with Pre stuff later?
  inputs (One X count) Γ = inputs count (renΓ weaken1Δ Γ)
  inputs (cumu count) Γ = inputs count Γ
  -- inputs none Γ = ⊤
  -- inputs (one {A} count) Γ = Nf Γ A × inputs count Γ

  data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) (renΓ weaken1Δ Γ) T → Nf Δ Γ (⋁ T)
    ne : ∀{n Δ Γ T} → Ne {n} Δ Γ T → Nf Δ Γ T
    cumu : ∀{Δ n T Γ}
      → Nf {n} Δ Γ T
      → Nf {suc n} Δ Γ (cumu T)

  data Ne : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    varapp : ∀{n Δ Γ T} → (count : ArgCount T)
      → (icx : InCtx Γ T)
      → inputs {n} {Δ} count Γ
      → Ne Δ Γ (output count)

idSubnApplyFact : ∀{n m Δ x} → Var x ≡ applySub {n} {m} (idSubn {n} {Δ}) x
idSubnApplyFact {_} {_} {_} {same} = refl
idSubnApplyFact {_} {_} {_} {next x} = cong (renType weaken1Δ) idSubnApplyFact

idSubnFact : ∀{n m Δ T} → T ≡ subTypen {n} {m} {Δ} {Δ} idSubn T
idSubnFact {_} {_} {_} {Var x} = idSubnApplyFact
idSubnFact {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ idSubnFact idSubnFact
idSubnFact {_} {_} {_} {⋁ T} = cong ⋁ idSubnFact -- NOTE: the implementation of TSub is key here, as liftTSub idSub = idSub DEFINITIONALLY
idSubnFact {_} {_} {_} {cumu T} = cong cumu idSubnFact

mutual
  -- subNf : ∀{} →
  appNf0 : ∀{Δ  Γ} → (T : Type 0 Δ)
    → Nf {0} Δ Γ T
    → (count : ArgCount T)
    → inputs count Γ
    → Nf Δ Γ (output count)
  appNf0 (A ⇒ B) (lambda e) (one count) (a , inputs)
    = appNf0 B {! subNf e same a  !} count inputs
  appNf0 T (ne x) (one count) (a , inputs) = {!   !}
  appNf0 T e none tt = e
  appNfS : ∀{n Δ Δ' Γ Tsubbed} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    -- → Tsubbed ≡ subTypen sub T
    → Nf {suc n} Δ Γ (subTypen sub T) -- Tsubbed
    → (count : ArgCount (subTypen sub T)) -- Tsubbed)
    → inputs count Γ
    → Nf Δ Γ (output count)
    -- crucial idea: we are doing induction on T, not e.
    -- we then do secondary recursion (not induction) on e, which should by all rights be harder but Agda is being nice here.
    -- then, the varapp and count=none case at the bottom is really a separate case for each type case.
    -- but thankfully Agda lets us combine them all into one case.
  appNfS (Var X) sub e count inputs = {!   !} -- really just have to prove sub X = X, so count = 0.
  appNfS (A ⇒ B) sub (lambda e) (one count) (a , inputs)
    = appNfS B sub {! subNf e same a  !} count inputs
  appNfS (⋁ T) sub (Tlambda e) (One X count) inputs
    = appNfS T (append1subn sub X) {! subNf sub e  !} {! subCount sub ecount  !} inputs
  appNfS (cumu T) sub (cumu e) count inputs = {! cumu  !}
  appNfS T sub (ne u{-varapp case-}) count inputs = {!   !}
  appNfS T sub e none tt = e

  appNf : ∀{n Δ Γ} → (T : Type n Δ)
    → Nf {n} Δ Γ T
    → (count : ArgCount T)
    → inputs count Γ
    → Nf Δ Γ (output count)
  appNf {zero} = appNf0
  appNf {suc n} T e count inputs
    -- = appNfS T idSubn (subst (λ T → Nf _ _ T) idSubnFact e) (subst ArgCount idSubnFact count) inputs
    = appNfS T idSubn (subst (λ T → Nf _ _ T) idSubnFact e) {! subst ArgCount idSubnFact count  !} {! inputs  !}


{-
TODO

1) The idea of this file is to have only appv and subv actually use Typos,
  everything else is just parametrized by regular stuff. But then, that means
  that Agda must be able to know that (subType sub T) can e.g. only give
  an ⇒ from an ⇒, and not from a Var. To do this, the sub must keep track of
  levels better. Because we will have the type of the sub be one less than the
  level of the type, so it could not come from a Var.


-------------------------------------------------------------------------------
  "PAPER" PROOF:

  If n = 0, then proof from S.T.L.C suffices, as no ∀ types.
  For all level n ≥ 1, for all typos (T , sub) where sub has vars at
  level (n-1) and for all e : sub(T), I will define
  (app e e₁ e₂ ... eₙ) for well types args, as well as
  e'[x ↦ e] for any well typed e'.

  The latter is easy, as it only depends on the former.

  For the former, cases on T:
  -- T = A ⇒ B. So, sub(T) = sub(A) ⇒ sub(B)
    then e = λ x . e' : sub(A) ⇒ sub(B)
    e₁ : A. Recurse with (n, A, sub, e₁) to get e'[x ↦ e₁] : B.
    Next, recurse with (n, B, sub, e'[x ↦ e₁]) to apply rest of args.
  -- T = ∀ X . A.   So, sub(T) = ∀ X . sub(A)
    then e = Λ X . e'  : ∀ X . sub(A)
    e₁ = A is a type.
    recurse on (n, A, sub ⊎ [X ↦ A] , e') to apply rest of args.
    NOTE: that A is at level (n-1), and so can only come up after a cumu.
    Therefore, X will be subbed for A by the time it comes up.
  -- T = X.  So sub(X) = X
    the can't be any well typed args. Keep in mind that X is at level n,
    and so sub(X) = X.
  -- T = cumu A. So, sub(cumu A) = cumu (sub(A))
    then e = cumu e'. Simply recurse with [n-1, sub(A), idSub, e']
    so need idSub(sub(A)) = sub(A) DEFINITIONALLY (or at least propositionally...)
-------------------------------------------------------------------------------

So, the takeaway is that it is crucial that sub be defined in a way so that
e.g. sub(A ⇒ B) = sub(A) ⇒ sub(B) is DEFINITIONALLY true.

We also need sub(X) = X, for X at level n+1 and sub at level n. DEFINITIONALLY
TODO: what does this even mean? the input and output will be in different Δ
It just means that the output must be a variable.

NOTE: I believe that these things are true of good ol' fashioned TSub?
Are they?

-}
