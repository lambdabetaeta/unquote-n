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

weakenRen1 : ∀{Δ₁ Δ₂ n} → TRen Δ₁ Δ₂ → TRen Δ₁ (Δ₂ , n)
weakenRen1 ren x = next (ren x)

liftTRen : ∀{Δ₁ Δ₂ n} → TRen Δ₁ Δ₂ → TRen (Δ₁ , n) (Δ₂ , n)
liftTRen ren same = same
liftTRen ren (next itc) = next (ren itc)

-- represents a type at level l
data Type : ℕ → TCtx →  Set where
  Var : ∀{Δ n} → InTCtx Δ n → Type n Δ
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
  ⋁ : ∀{n Δ} → Type (suc n) (Δ , n) → Type (suc n) Δ
  cumu : ∀{n Δ} → Type n Δ → Type (suc n) Δ

renType : ∀{n Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type n Δ₁ → Type n Δ₂
renType ren (Var x) = Var (ren x)
renType ren (A ⇒ B) = renType ren A ⇒ renType ren B
renType ren (⋁ T) = ⋁ (renType (liftTRen ren) T)
renType ren (cumu T) = cumu (renType ren T)

data Ctx : Set where
  ∅ : Ctx
  _,_ : ∀{n Δ} → Ctx → Type n Δ → Ctx

  -- TODO: I'm making a decision that cumu will be in Type, and
  -- cumu AND weakenΔ will be in Exp. Hopefully I don't regret that.

data SameTypes : ∀{nA nB ΔA ΔB} → Type nA ΔA → Type nB ΔB → Set where
  refl : ∀{n Δ} → {T : Type n Δ} → SameTypes T T

-- data InCtx : ∀{n Δ} → Ctx → Type n Δ → Set where
--   weakenΔ : ∀{n Δ Γ T m}
--     → InCtx {n} {Δ} Γ T → InCtx {n} {Δ , m} Γ (renType (weaken1Δ) T)
--   same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
--
-- data InCtx2 : ∀{n Δ} → Ctx → Type n Δ → Set where
--   weakenΓ : ∀{n Δ Γ T m} → {A : Type m Δ}
--     → InCtx2 {n} {Δ} Γ T → InCtx2 {n} {Δ} (Γ , A) T
--   inctx : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → InCtx2 Γ T
--
-- subCtx : ∀{n Δ Γ T} → (icx : InCtx {n} {Δ} Γ T) → Ctx
-- subCtx (weakenΔ x) = subCtx x
-- subCtx (same {_} {_} {Γ}) = Γ
--
-- subCtx2 : ∀{n Δ Γ T} → (icx : InCtx2 {n} {Δ} Γ T) → Ctx
-- subCtx2 (weakenΓ {_} {_} {_} {_} {_} {A} icx) = subCtx2 icx , A
-- subCtx2 (inctx {_} {_} {Γ} x) = subCtx x
--
-- varSub : ∀{ΔA ΔB Γ nA nB} → {A : Type nA ΔA} → {B : Type nB ΔB}
--   → (icx : InCtx {nA} {ΔA} Γ A)
--   → (x : InCtx Γ B) → (SameTypes B A) ⊎ (InCtx (subCtx icx) B)
-- varSub same same = inj₁ refl
-- varSub same (weakenΔ x) = inj₂ {!   !}
-- varSub (weakenΔ icx) same = inj₂ {! same  !}
-- varSub (weakenΔ icx) (weakenΔ x) = {!   !}
--
-- varSub2 : ∀{ΔA ΔB Γ nA nB} → {A : Type nA ΔA} → {B : Type nB ΔB}
--   → (icx : InCtx2 {nA} {ΔA} Γ A)
--   → (x : InCtx2 Γ B) → (SameTypes B A) ⊎ (InCtx2 (subCtx2 icx) B)
-- varSub2 (inctx icx) (inctx x) = {! varSub icx x  !}
-- varSub2 (weakenΓ icx) (inctx x) = {!   !}
-- varSub2 (inctx icx) (weakenΓ x) = {!   !}
-- varSub2 (weakenΓ icx) (weakenΓ x) = {!   !}

data InCtx : ∀{n Δ} → Ctx → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ ΔT Γ A} → {T : Type m ΔT}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A
subCtx : ∀{n Δ Γ T} → (icx : InCtx {n} {Δ} Γ T) → Ctx
subCtx (same {_} {_} {Γ}) =  Γ
subCtx (next {_} {_} {_} {_} {_} {_} {T} icx) = subCtx icx , T


-- left means use toSub, right means just adjust x for new context.
varSub : ∀{ΔA ΔB Γ nA nB} → {A : Type nA ΔA} → {B : Type nB ΔB}
  → (icx : InCtx {nA} {ΔA} Γ A)
  → (x : InCtx Γ B) → (SameTypes B A) ⊎ (InCtx (subCtx icx) B)
varSub same same = inj₁ refl
varSub same (next x) = inj₂ x
varSub (next icx) same = inj₂ same
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ x' = inj₂ (next x')

-- subCtx2 : ∀{n Δ Γ T} → (icx : InCtx2 {n} {Δ} Γ T) → Ctx
-- subCtx2 (weakenΔ icx) = subCtx2 icx
-- subCtx2 (inctx x) = subCtx x
-- -- TODO NEXT: get varSub to work for InCtx2.
-- varSub2 : ∀{ΔA ΔB Γ nA nB} → {A : Type nA ΔA} → {B : Type nB ΔB}
--   → (icx : InCtx2 {nA} {ΔA} Γ A)
--   → (x : InCtx2 Γ B) → (SameTypes B A) ⊎ (InCtx2 (subCtx2 icx) B)
-- varSub2 (weakenΔ icx) (weakenΔ x) with varSub2 icx x
-- ... | res = {!   !}
-- varSub2 (weakenΔ icx) (inctx x) = {! varSub2 icx (inctx x)  !}
-- varSub2 (inctx x₁) (weakenΔ x) = {!   !}
-- varSub2 (inctx x₁) (inctx x) with varSub x₁ x
-- ... | inj₁ p = inj₁ p
-- ... | inj₂ y = inj₂ (inctx y)

data TSubn : ℕ → TCtx → TCtx → Set where
  ∅ : ∀{n} → TSubn n ∅ ∅
  nextn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
  nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , m) (Δ₂ , m)

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


------------------------------------------------------------------------------------
-------------    UGLY LEMMA ZONE

idSubnApplyFact : ∀{n m Δ x} → Var x ≡ applySub {n} {m} (idSubn {n} {Δ}) x
idSubnApplyFact {_} {_} {_} {same} = refl
idSubnApplyFact {_} {_} {_} {next x} = cong (renType weaken1Δ) idSubnApplyFact

idSubnFact : ∀{n m Δ T} → T ≡ subTypen {n} {m} {Δ} {Δ} idSubn T
idSubnFact {_} {_} {_} {Var x} = idSubnApplyFact
idSubnFact {_} {_} {_} {A ⇒ B} = cong₂ _⇒_ idSubnFact idSubnFact
idSubnFact {_} {_} {_} {⋁ T} = cong ⋁ idSubnFact -- NOTE: the implementation of TSub is key here, as liftTSub idSub = idSub DEFINITIONALLY
idSubnFact {_} {_} {_} {cumu T} = cong cumu idSubnFact

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

bigLemmaApply : ∀{Δ Δ' n m} → (l : List ℕ) → (sub : TSubn n Δ' Δ)
  → (x : InTCtx (appendMany (Δ' , n) l) m) → {X : Type n Δ}
  → (subTypen (liftManySub l (append1subn idSubn X)) (applySub (liftManySub l (liftTSubn sub)) x))
    ≡ (applySub (liftManySub l (append1subn sub X)) x)
bigLemmaApply [] ∅ same = refl
bigLemmaApply (x₁ ∷ l) ∅ same = refl
bigLemmaApply (x₁ ∷ l) ∅ (next x) = {! bigLemmaApply  !}
bigLemmaApply l (nextn sub x₁) x = {! x  !}
bigLemmaApply l (nextm sub) x = {! x  !}

bigLemma : ∀{Δ Δ' n m} → {sub : TSubn n Δ' Δ} → (l : List ℕ)
  → (T : Type m (appendMany (Δ' , n) l)) → {X : Type n Δ}
  → (subTypen (liftManySub l (append1subn idSubn X)) (subTypen (liftManySub l (liftTSubn sub)) T))
    ≡ (subTypen (liftManySub l (append1subn sub X)) T)
bigLemma l (Var x) = bigLemmaApply l _ x
bigLemma l (A ⇒ B) = cong₂ _⇒_ (bigLemma l A) (bigLemma l B)
bigLemma l (⋁ T) = cong ⋁ (bigLemma (_ ∷ l) T)
bigLemma l (cumu T) = cong cumu (bigLemma l T)

---------------------------------------------------------------------------------------

idRen : ∀{Δ} → TRen Δ Δ
idRen same = same
idRen (next x) = next (idRen x)

renMany : ∀{Δ} → (l : List ℕ) → TRen Δ (appendMany Δ l)
renMany [] = idRen
renMany (n ∷ l) = weakenRen1 (renMany l)

data InCtx2 : ∀{n Δ} → Ctx → Type n Δ → Set where
  -- weakenΔ : ∀{n Δ Γ T m} → InCtx2 {n} {Δ} Γ T → InCtx2 {n} {Δ , m} Γ (renType (weaken1Δ) T)
  inctx : ∀{n Δ Γ T} → (weakenBy : List ℕ) → InCtx {n} {Δ} Γ T
    → InCtx2 {n} {appendMany Δ weakenBy} Γ (renType (renMany weakenBy) T)
  -- NOTE: we need it to be programmed like this, because we will use the weakenBy
  -- To also weaken the Nf later. Which means we need renNf, make sure thats possible.

data Exp : ∀{n} → (Δ : TCtx) → Ctx → Type n Δ → Set where
  var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{n Δ Γ A B} → Exp {n} Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Tlambda : ∀{Δ n Γ T}
    → Exp (Δ , n) Γ T → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subTypen (append1subn idSubn X) T)
  cumu : ∀{Δ n T Γ}
    → Exp {n} Δ Γ T
    → Exp {suc n} Δ Γ (cumu T)


mutual
  data Nf : ∀{n} → (Δ : TCtx) → Ctx → Type n Δ → Set where
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) Γ T → Nf Δ Γ (⋁ T)
    ne : ∀{n Δ Γ T nOut TOut}
      → (x : InCtx2 {n} Γ T)
      → (args : Args Γ T nOut TOut)
      → Nf Δ Γ TOut
    -- weakenΔ : ∀{n Δ Γ T m} → Nf {n} Δ Γ T → Nf {n} (Δ , m) Γ (renType (weaken1Δ) T)
    cumu : ∀{Δ n T Γ}
      → Nf {n} Δ Γ T
      → Nf {suc n} Δ Γ (cumu T)

-- TODO: make nOut hidden arg
--                              T         ↓ outputN    ↓ output type
  data Args : ∀{n Δ} → Ctx → Type n Δ → (nOut : ℕ) → Type nOut Δ  → Set where
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

-- TODO: Do I need this? (and therefore liftCommType and liftCommΓ as well?)
-- NOTE: its actually not possible to define this due to the way that contexts work.
-- renNf : ∀{n Δ₁ Δ₂ Γ T} → (ren : TRen Δ₁ Δ₂)
--   → Nf {n} Δ₁ Γ T → Nf Δ₂ Γ (renType ren T)
-- renNf ren (lambda e) = {! lambda  !} -- lambda (renNf ren e)
-- renNf ren (Tlambda e) = Tlambda (renNf (liftTRen ren) e)
-- renNf ren (cumu e) = cumu (renNf ren e)
-- renNf ren (ne x args) = {!   !}

renNf : ∀{n Δ₁ Δ₂ Γ T} → (ren : TRen Δ₁ Δ₂)
  → Nf {n} Δ₁ Γ T → Nf Δ₂ Γ (renType ren T)
renNf ren (lambda e) = lambda (renNf ren {! e  !} ) -- need to be able to ren Δ in Γ term or something.....
renNf ren (Tlambda e) = {!   !}
renNf ren (ne x args) = {!   !}
renNf ren (cumu e) = {!   !}

mutual
  -- subNf : ∀{n n' Δ Δx Γ T'} → (T : Type n Δx) → (x : InCtx Γ T)
  --   → (toSub : Nf {n} Δx (subCtx x) T)
  --   → Nf {n'} Δ Γ T' → Nf Δ (subCtx x) T'
  -- subNf T x toSub (lambda e) = lambda (subNf T (next x) {! weaken toSub  !} e)
  -- subNf T x toSub (Tlambda e) = Tlambda (subNf T x toSub e)
  -- subNf T x toSub (cumu e) = cumu (subNf T x toSub e)
  -- subNf T x toSub (ne y args) with varSub x y
  -- ... | inj₁ refl = appNf T toSub {! args  !}
  -- ... | inj₂ y' = {!   !}

  subNf0 : ∀{n' Δ Δx Γ T'} → (T : Type 0 Δx) → (x : InCtx Γ T)
    → (toSub : Nf {0} Δx (subCtx x) T)
    → Nf {n'} Δ Γ T' → Nf Δ (subCtx x) T'
  subNf0 T x toSub (lambda e) = lambda (subNf0 T (next x) {! weaken toSub  !} e)
  subNf0 T x toSub (Tlambda e) = Tlambda (subNf0 T x toSub e)
  subNf0 T x toSub (cumu e) = cumu (subNf0 T x toSub e)
  subNf0 T x toSub (ne y args) = {! varSub x y  !}
  -- subNf0 T x toSub (ne y args) with varSub x y
  -- ... | inj₁ refl = appNf0 T toSub (subArgs0 T x toSub args)
  -- ... | inj₂ y' = ne y' (subArgs0 T x toSub args)

  subArgs0 : ∀{n' l Δ Δx Γ T' T₁} → (T : Type 0 Δx) → (x : InCtx Γ T)
    → (toSub : Nf {0} Δx (subCtx x) T)
    → Args {l} {Δ} Γ T₁ n' T' → Args (subCtx x) T₁ n' T'
  subArgs0 T x toSub none = none
  subArgs0 T x toSub (one args e) = one (subArgs0 T x toSub args) (subNf0 T x toSub e)
  subArgs0 T x toSub (One X args) = One X (subArgs0 T x toSub args)
  subArgs0 T x toSub (cumu args) = cumu (subArgs0 T x toSub args)

  appNf0 : ∀{Δ  Γ nOut TOut} → (T : Type 0 Δ)
    → Nf {0} Δ Γ T
    → Args Γ T nOut TOut
    → Nf Δ Γ TOut
  appNf0 (A ⇒ B) (lambda e) (one args a) = appNf0 B (subNf0 A same a e) args
  appNf0 T (ne x args₁) args₂ = ne x (joinArgs args₁ args₂)
  appNf0 T e none = e

  appNfS : ∀{n Δ Δ' Γ nOut TOut} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → Nf {suc n} Δ Γ (subTypen sub T) -- Tsubbed
    → (args : Args Γ (subTypen sub T) nOut TOut) -- Tsubbed)
    → Nf Δ Γ TOut
    -- crucial idea: we are doing induction on T, not e.

  appNfS (Var X) sub e args = {!   !} -- really just have to prove sub X = X, so args = 0.
  appNfS (A ⇒ B) sub (lambda e) (one args a)
    -- = appNfS B sub (subNf A same ? e) args
    -- TODO TODO TODO TODO: it is essential that subNf takes subs as args, or else isn't actually
    -- a proof, because isn't decreasing on types/levels!!!!
    -- = appNfS B sub (subNf (subTypen sub A) same a e) args
    = {!   !}
  appNfS (⋁ T) sub (Tlambda e) (One X args)
    = {! e  !}
    -- = appNfS T (append1subn sub X) (let e' = subNfTSubn (append1subn idSubn X) e
    --   in {! e'  !} ) -- subRenCancelΓ, and one more thing
    --   {! args  !}
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
