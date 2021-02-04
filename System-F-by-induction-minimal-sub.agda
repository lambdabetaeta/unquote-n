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

-- TODO: in this file, going to use Typo specifically only for appv and subv

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
output (One X count) = subType (append1sub idSub X) (output count)
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

-- -- TODO: call TSub, call the subv ESub. (expression and type)
-- subNf : ∀{n Δ₁ Δ₂ Γ T} → (sub : TSub Δ₁ Δ₂)
--   → Nf {n} Δ₁ Γ T
--   → Nf {n} Δ₂ (subΓ sub Γ) (subType sub T)
-- subNf sub (lambda e) = lambda (subNf sub e)
-- subNf {n} {Δ₁} {Δ₂} {Γ} {T} sub (Tlambda e)
--   = Tlambda {! subNf {n} {Δ₁ , n} {Δ₂ , n} ? ?  !}
-- subNf sub (ne (varapp count icx x)) = {!   !}
-- subNf sub (cumu e) = {!   !}

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

TSubn : ℕ → TCtx → TCtx → Set
TSubn n Δ₁ Δ₂ = ∀{m}
  -- → case n ≟ m of
  --   λ { (yes x) → InTCtx Δ₁ m → Type m Δ₂ -- or n, not sure which is better
  --     ; (no  y) → InTCtx Δ₁ m → InTCtx Δ₂ m
  --   }
  → (n ≡ m → InTCtx Δ₁ m → Type m Δ₂) × (¬ n ≡ m → InTCtx Δ₁ m → InTCtx Δ₂ m)

liftTSubn1 : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂
  → ∀{m} → n ≡ m → InTCtx (Δ₁ , l) m → Type m (Δ₂ , l)
liftTSubn1 sub p same = Var same
liftTSubn1 sub p (next x) = renType weaken1Δ ((proj₁ sub) p x)
liftTSubn2 : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂
  → ∀{m} → ¬ n ≡ m → InTCtx (Δ₁ , l) m → InTCtx (Δ₂ , l) m
liftTSubn2 sub p same = same
liftTSubn2 sub p (next x) = next ((proj₂ sub) p x)
liftTSubn : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , l) (Δ₂ , l)
liftTSubn {n} {l} sub
  = liftTSubn1 sub , liftTSubn2 sub

subTypen : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
subTypen {n} {m} sub (Var x) = case n ≟ m of
  λ { (yes p) → (proj₁ sub) p x
    ; (no p) → Var ((proj₂ sub) p x)
  }
subTypen sub (A ⇒ B) = subTypen sub A ⇒ subTypen sub B
subTypen sub (⋁ T) = ⋁ (subTypen (liftTSubn sub) T)
subTypen sub (cumu T) = cumu (subTypen sub T)

subCtxn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subCtxn sub ∅ = ∅
subCtxn sub (Γ , T) = subCtxn sub Γ , subTypen sub T

subNfn : ∀{n m Δ₁ Δ₂ Γ T} → (sub : TSubn n Δ₁ Δ₂) → Nf {m} Δ₁ Γ T
  → Nf Δ₂ (subCtxn sub Γ) (subTypen sub T)
subNfn sub (lambda e) = lambda (subNfn sub e)
subNfn sub (Tlambda e) = Tlambda {! subNfn (liftTSubn sub) e  !}
subNfn sub (ne x) = {!   !}
subNfn sub (cumu e) = cumu (subNfn sub e)

idSubn : ∀{n Δ} → TSubn n Δ Δ
idSubn = (λ p x → Var x) , λ p x → x

idSubnFact : ∀{n m Δ T} → T ≡ subTypen {n} {m} {Δ} {Δ} idSubn T
idSubnFact = {!   !}
-- idSubnFact {_} {_} {_} {Var x} = {!   !}
-- idSubnFact {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ idSubnFact idSubnFact
-- idSubnFact {_} {_} {_} {⋁ T} = cong ⋁ {!   !}
-- idSubnFact {_} {_} {_} {cumu T} = {!   !}

append1subn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
append1subn {n} sub T {m} = case n ≟ m of
  λ { (yes p) → (λ _ → λ { same → T -- why oh why aren't there normal case expressions in Agda
                          ; (next x) → proj₁ sub p x
                        })
      , λ np → ⊥-elim (np p)
    ; (no np) → (λ p → ⊥-elim (np p)) , λ _ → λ { same → ⊥-elim (np refl)
                                                ; (next x) → proj₂ sub np x
                                                  }
  }


-- mutual
  -- appv : ∀{n Δ Γ T} → (ext : TCtxExt Δ) → (sub : ExtSub {Δ} ext)
    -- → Nf {n} Δ Γ (subExt sub T)

-- mutual
--   --             ↓
--   -- subv1 : ∀{n m Δ Δ' Γ Te Tsub Tsub'} → {sub : TSub Δ' Δ}
--   --   → Tsub' ≡ subType sub Tsub
--   --   → (icx : InCtx {n} {Δ} Γ Tsub')
--   --   → (toSub : Nf Δ (subCtx icx) Tsub')
--   --   → Nf {m} Δ Γ Te → Nf Δ (subCtx icx) Te
--   -- subv1 = {!   !}
--   --           ↓           ↓                ↓   makes a Typo
--   appv1 : ∀{n Δ Δ' Γ} → (T : Type n Δ') → (sub : TSub Δ' Δ)
--     → (e : Nf {n} Δ Γ (subType sub T))
--     → (count : ArgCount (subType sub T)) -- TODO: wrong, wont allow full application of e.g. ∀X . X → X
--     → inputs count Γ
--     → Nf Δ Γ (output count)
--   appv1 (A ⇒ B) sub (lambda e) none tt = {!   !} -- subNf sub (lambda e)
--   appv1 (A ⇒ B) sub (lambda e) (one count) (a , inputs)
--     = appv1 B sub {! subv1 sub a e  !} count inputs
--   appv1 (⋁ T) sub (Tlambda e) none tt = {!   !} -- subNf sub (Tlambda e)
--   appv1 (⋁ T) sub (Tlambda e) (One X count) inputs
--     = let a = appv1 T (append1sub sub X)
--               {!   !} {!   !} {-count-} inputs
--       in {! a  !} -- Same as lambda case, need to do sub and app. Just that its a type sub!
--   appv1 T sub (ne x) count inputs = {!   !}
--   appv1 (cumu T) sub (cumu e) none inputs = {!   !} -- subNf sub (cumu e)
--   appv1 (cumu T) sub (cumu e) (cumu count) inputs
--     = appv1 T sub e count inputs -- TODO this is wrong, should be applying sub.

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
    = {!   !}
    -- = appNfS T (append1subn sub X) {! subNf sub e  !} {! subCount sub ecount  !} inputs
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
    = {!   !}
    -- = appNfS T idSubn (subst (λ T → Nf _ _ T) idSubnFact e) (subst ArgCount idSubnFact count) inputs


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
