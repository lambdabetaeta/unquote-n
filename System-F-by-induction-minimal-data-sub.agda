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

nfToExp : ∀{n Δ Γ T} → Nf {n} Δ Γ T → Exp {n} Δ Γ T
nfToExp (lambda e) = lambda (nfToExp e)
nfToExp (Tlambda e) = Tlambda (nfToExp e)
nfToExp (ne x args) = {!   !}
nfToExp (cumu e) = cumu (nfToExp e)

idSubnApplyFact : ∀{n m Δ x} → Var x ≡ applySub {n} {m} (idSubn {n} {Δ}) x
idSubnApplyFact {_} {_} {_} {same} = refl
idSubnApplyFact {_} {_} {_} {next x} = cong (renType weaken1Δ) idSubnApplyFact

idSubnFact : ∀{n m Δ T} → T ≡ subTypen {n} {m} {Δ} {Δ} idSubn T
idSubnFact {_} {_} {_} {Var x} = idSubnApplyFact
idSubnFact {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ idSubnFact idSubnFact
idSubnFact {_} {_} {_} {⋁ T} = cong ⋁ idSubnFact -- NOTE: the implementation of TSub is key here, as liftTSub idSub = idSub DEFINITIONALLY
idSubnFact {_} {_} {_} {cumu T} = cong cumu idSubnFact

mutual
  subNf : ∀{n n' Δ Γ T T'} → (x : InCtx Γ T)
    → (toSub : Nf {n} Δ (subCtx x) T)
    → Nf {n'} Δ Γ T' → Nf Δ (subCtx x) T'
  subNf x toSub (lambda e) = lambda (subNf (next x) {!  toSub !} e)
  subNf x toSub (Tlambda e) = Tlambda {!   !} -- (subNf {! x  !} {! toSub  !} e)
  subNf x toSub (ne icx args) = {!   !}
  subNf x toSub (cumu e) = cumu (subNf x toSub e)
  appNf0 : ∀{Δ  Γ nOut TOut} → (T : Type 0 Δ)
    → Nf {0} Δ Γ T
    → (count : Args Γ T nOut TOut)
    → Nf Δ Γ TOut
  appNf0 (A ⇒ B) (lambda e) (one count a)
    = appNf0 B (subNf same a e) count
  appNf0 T (ne x args) (one a count) = {!   !}
  appNf0 T e none = e
  appNfS : ∀{n Δ Δ' Γ Tsubbed nOut TOut} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    -- → Tsubbed ≡ subTypen sub T
    → Nf {suc n} Δ Γ (subTypen sub T) -- Tsubbed
    → (count : Args Γ (subTypen sub T) nOut TOut) -- Tsubbed)
    → Nf Δ Γ TOut
    -- crucial idea: we are doing induction on T, not e.

  appNfS (Var X) sub e count = {!   !} -- really just have to prove sub X = X, so count = 0.
  appNfS (A ⇒ B) sub (lambda e) (one count a)
    = appNfS B sub (subNf same a e) count
  appNfS (⋁ T) sub (Tlambda e) (One X count)
    = appNfS T (append1subn sub X) {! e  !} {! count  !}
  appNfS (cumu T) sub (cumu e) (cumu count)
    = appNf (subTypen sub T) e count
  appNfS T sub (ne x args) count = {!   !}
  appNfS T sub e none = e

  appNf : ∀{n Δ Γ nOut TOut} → (T : Type n Δ)
    → Nf {n} Δ Γ T
    → (count : Args Γ T nOut TOut)
    → Nf Δ Γ TOut
  appNf {zero} = appNf0
  appNf {suc n} {Δ} {Γ} {nOut} {TOut} T e count
    = appNfS T idSubn
      (subst (λ T → Nf _ _ T) idSubnFact e)
      (subst (λ T → Args Γ T nOut TOut) idSubnFact count)

{-
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
    so e' : sub(A), so [X ↦ A]e : (sub ⊎ [X ↦ A])T       THIS JUDGEMENT HERE IS WHATS HARD
    e₁ = A is a type.
    recurse on (n, A, sub ⊎ [X ↦ A] , [X ↦ A]e') to apply rest of args.
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

PLAN: TODO:
In several cases, there is a pattern of substituting from something that is weakened.
Currently, we have
Sub : Exp Γ → Exp (smaller Γ)

Consider
Sub : Exp (weakened Γ) → Exp Γ


IDEA:
Δ₁    Δ₂
X ⇔  A
Y ⇔  B
      C
Z ⇔  D
      E

Is a renaming Δ₁ → Δ₂ - really a WEAKENING, not a renaming
To sub Δ₂ → Δ₁, only have to supply missing types, so C and E.
-}

-- DO I really need ANY weakening and not just single weakenings?
data Weakening : ℕ → TCtx → TCtx → Set where
  ∅ : ∀{n} → Weakening n ∅ ∅
  same : ∀{n Δ₁ Δ₂ i} → Weakening n Δ₁ Δ₂ → Weakening n (Δ₁ , i) (Δ₂ , i)
  skip : ∀{n Δ₁ Δ₂} → Weakening n Δ₁ Δ₂ → Weakening n Δ₁ (Δ₂ , n)

data TSub3 : ∀{n Δ₁ Δ₂} → Weakening n Δ₂ Δ₁ → Set where
  ∅ : ∀{n} → TSub3 {n} ∅
  same : ∀{n Δ₁ Δ₂ i wea} → TSub3 {n} {Δ₁} {Δ₂} wea → TSub3 (same {_} {_} {_} {i} wea)
  skip : ∀{n Δ₁ Δ₂ wea} → TSub3 {n} {Δ₁} {Δ₂} wea
    → Type n Δ₂ → TSub3 (skip wea)

data Ctx' : TCtx → Set where
  ∅ : Ctx' ∅
  _,_ : ∀{n Δ} → Ctx' Δ → Type n Δ → Ctx' Δ
  lift : ∀{Δ n} → Ctx' Δ → Ctx' (Δ , n)

-- TODO: whenever I look at this: think about if Ctx' could actually solve issue.
-- The idea is that lift constructor is used in Nf definition in place of
-- weakening the context with a function. Then this somehow makes types work out
-- in subNf later. Note that this also makes contexts so that they can store
-- types in weaker Δs in them. This plan smells fishy because in dep. thy.
-- it makes no sense, there is only one context, and each thing in it has context
-- everything previous to it. Maybe this actually makes it more similar to dep thy?
-- Maybe consider combining contexts?
weakenΓ' : ∀{Δ Δ' n} → Weakening n Δ Δ'
  → Ctx' Δ → Ctx' Δ'
weakenΓ' (same wea) (lift Γ) = lift (weakenΓ' wea Γ)
weakenΓ' ∅ ∅ = ∅
weakenΓ' (skip wea) ∅ = {! skip (weakenΓ' wea ∅)  !}
weakenΓ' wea (Γ , x) = {!   !}
weakenΓ' wea (lift Γ) = {!   !}

idWea : ∀{n Δ} → Weakening n Δ Δ
idWea {n} {∅} = ∅
idWea {n} {Δ , T} = same idWea

idSub3 : ∀{n Δ} → TSub3 {n} {Δ} idWea
idSub3 {n} {∅} = ∅
idSub3 {n} {Δ , T} = same idSub3

applySub3 : ∀{n m Δ₁ Δ₂} → (wea : Weakening n Δ₂ Δ₁) → TSub3 wea → InTCtx Δ₁ m → Type m Δ₂
applySub3 .(same _) (same sub) same = Var same
applySub3 .(same _) (same sub) (next x) = renType weaken1Δ (applySub3 _ sub x)
applySub3 {n} {m} {Δ₁} {Δ₂} .(skip _) (skip sub T) same = T
applySub3 .(skip _) (skip sub T) (next x) = applySub3 _ sub x

subType3 : ∀{n Δ Δ' m} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Type m Δ' → Type m Δ
subType3 wea sub (Var x) = applySub3 wea sub x
subType3 wea sub (A ⇒ B) = subType3 wea sub A ⇒ subType3 wea sub B
subType3 wea sub (⋁ T) = ⋁ (subType3 (same wea) (same sub) T)
subType3 wea sub (cumu T) = cumu (subType3 wea sub T)

subΓ3 : ∀{n Δ Δ'} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Ctx Δ' → Ctx Δ
subΓ3 wea sub ∅ = ∅
subΓ3 wea sub (Γ , T) = subΓ3 wea sub Γ , subType3 wea sub T

subNf3 : ∀{n Δ Δ' m Γ T} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Nf Δ' Γ T
 → Nf {m} Δ (subΓ3 _ sub Γ) (subType3 _ sub T)
subNf3 wea sub (lambda e) = lambda (subNf3 _ sub e)
subNf3 wea sub (Tlambda e) = Tlambda {! subNf3 (same wea) (same sub) e  !}
subNf3 wea sub (cumu e) = {!   !}
subNf3 wea sub (ne x args) = {!   !}

-- ALTERNATE IDEA:

weakenType : ∀{Δ Δ' n m} → Weakening n Δ Δ'
  → Type m Δ → Type m Δ'
weakenType = {!   !}

weakenΓ : ∀{Δ Δ' n} → Weakening n Δ Δ'
  → Ctx Δ → Ctx Δ'
weakenΓ = {!   !}

subNf3' : ∀{n Δ Δ' m Γ T} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Nf Δ' (weakenΓ wea Γ) (weakenType wea T)
 → Nf {m} Δ Γ T
subNf3' = {!   !}

-- THIS ONE IS CORRECT.
-- Need to combine with Sub as list of 1Sub, as in comment in other file.
subNf3'' : ∀{n Δ Δ' m Γ T} → (wea : Weakening n Δ Δ') → (sub : TSub3 wea)
 → Nf Δ' (weakenΓ wea Γ) T
 → Nf {m} Δ Γ (subType3 wea sub T)
subNf3'' = {!   !}

subNf3''' : ∀{n Δ Δ' m Γ} → (T : Type m (Δ' , n)) → (X : Type n Δ) → (wea : Weakening n Δ Δ')
  → (sub : TSub3 wea)
 → Nf (Δ , n) (weakenΓ (skip idWea) Γ) (subType3 (same wea) (same sub) T)
 → Nf {m} Δ Γ (subType3 (skip wea) (skip sub X) T)
subNf3''' T X .∅ ∅ e = {! subNf3 ...   !} -- requires (weaken idWea)
subNf3''' T X .(same _) (same sub) e = {! weaken (subNf3''' _ sub e)  !}
subNf3''' T X .(skip _) (skip sub x) e = {!   !}

appNfS3 : ∀{n Δ Δ' Γ Tsubbed nOut TOut}
  → (wea : Weakening n Δ Δ')
  → (sub : TSub3 wea) -- from Δ' → Δ, opposite direction from weakening
  → (T : Type (suc n) Δ')
  → Nf {suc n} Δ Γ (subType3 wea sub T) -- (subType3 sub T)
  → (count : Args Γ (subType3 wea sub T) nOut TOut)
  → Nf Δ Γ TOut
appNfS3 wea sub (Var x) e count = {!   !} -- prove that sub X = Var Y, so count = 0
appNfS3 wea sub (A ⇒ B) (lambda e) (one count a)
  = appNfS3 wea sub B (subNf same a e) count
appNfS3 wea sub (⋁ T) (Tlambda e) (One X count)
  -- = appNfS3 (skip wea) (skip sub X) T (subNf3' (skip idWea) (skip idSub3 X) {! e  !} ) {! count  !}
  -- NOTE: constraint that appears from below line
  -- = appNfS3 (skip wea) (skip sub X) T (subNf3'' (skip idWea) (skip idSub3 X) {! e  !}) {! count  !}
  = appNfS3 (skip wea) (skip sub X) T
    -- (subNf3''' T X wea sub e)
    (subNf3''' T X wea sub {! e  !} )
    {! count  !}
appNfS3 wea sub (cumu T) (cumu e) (cumu count)
  = appNf (subType3 wea sub T) e count
appNfS3 wea sub T e none = e
appNfS3 wea sub T (ne x args) count = {!   !}

-- Then, for e case of TLambda case of appNfS, need
-- subΓ (skip idSub) (weakenΓ (skip idWeak) Γ) = Γ
-- subType (skip idSub) (subType (liftTSubn sub) T)
--    = (subTypen (append1susbn sub X) T)

-- idSub = same same same ..., and liftTSubn = same, append1subn = skip
--
-- IDEA: prevent ever having to use idSub and idRen by making subs and weaks
-- only one position instead of all/any.

{-
 To recap for later,

 I had this idea about how to make the e and count args of TLambda case easier.
 Basically it boiled down to instead of appNfS being defined on ALL Δ, Δ'
 instead I define weakenings, and define it on only specifically Δ' a weakening of Δ
 Then Sub is defined in the reverse direction of weakenings.
 What remains to see if it works is to
  -- define subNf3.
  -- May also need to redo renamings from earlier as just simple single weakenings,
      a. la. my original STLC by induction.
  -- Or possibly, just make the weakenings from earlier in the file use these new weakenings.

  In fact, plan for tommorow:
  1) make new file copy
  2) Delete old TRen, replace entirely with Weakening
  3) See if I can get e and count cases to work in appNfS3.
      In e case, at worst, T arg doesn't work, rest definitely do.
  4) For count case, will need "subArgs", defined similarly on weakenings like subType3.
-}

{-
TODO: think about these things in terms of paper proof again.
-}
