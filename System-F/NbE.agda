open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)
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

data Ctx : TCtx → Set where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{n Δ} → Ctx Δ → Type n Δ → Ctx Δ

renΓ : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renΓ ren ∅ = ∅
renΓ ren (Γ , T) = renΓ ren Γ , renType ren T

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
    → Exp Δ Γ (subTypen (append1subn idSubn X) T)

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

mutual
  data Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    lambda : ∀{n Δ Γ A B} → Nf {n} Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
    Tlambda : ∀{Δ n Γ T}
      → Nf (Δ , n) (renΓ weaken1Δ Γ) T → Nf Δ Γ (⋁ T)
    ne : ∀{n Δ Γ T} → Ne {n} Δ Γ T → Nf Δ Γ T
    cumu : ∀{Δ n T Γ}
      → Nf {n} Δ Γ T
      → Nf {suc n} Δ Γ (cumu T)

  data Ne : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Ne Δ Γ T
    app : ∀{n Δ Γ A B} → Ne {n} Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B
    TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
      → Ne Δ Γ (⋁ T)
      → (X : Type n Δ)
      → Ne Δ Γ (subTypen (append1subn idSubn X) T)

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
bigLemmaApply = {!   !}

bigLemma : ∀{Δ Δ' n m} → {sub : TSubn n Δ' Δ} → (l : List ℕ)
  → (T : Type m (appendMany (Δ' , n) l)) → {X : Type n Δ}
  → (subTypen (liftManySub l (append1subn idSubn X)) (subTypen (liftManySub l (liftTSubn sub)) T))
    ≡ (subTypen (liftManySub l (append1subn sub X)) T)
bigLemma l (Var x) = bigLemmaApply l _ x
bigLemma l (A ⇒ B) = cong₂ _⇒_ (bigLemma l A) (bigLemma l B)
bigLemma l (⋁ T) = cong ⋁ (bigLemma (_ ∷ l) T)
bigLemma l (cumu T) = cong cumu (bigLemma l T)

---------------------------------------------------------------------------------------

mutual
  SemS : ∀{n Δ Δ'} → (Γ : Ctx Δ) → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → Set
  SemS Γ (Var x) sub = Nf _ Γ (applySub sub x)
  SemS Γ (A ⇒ B) sub = GExpS Γ A sub → SemS Γ B sub
  SemS {n} {Δ} Γ (⋁ T) sub = (X : Type n Δ) → SemS Γ T (nextn sub X)
  SemS Γ (cumu T) sub = Sem Γ (subTypen sub T)

  Sem : ∀{n Δ} → (Γ : Ctx Δ) → (T : Type n Δ) → Set
  Sem {zero} Γ (Var x) = Nf _ Γ (Var x) -- TODO: is this right?
  Sem {zero} Γ (A ⇒ B) = GExp _ Γ A → Sem Γ B
  Sem {suc n} Γ T = SemS Γ T idSubn

  GExp : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set
  GExp Δ Γ T = ∀{Γ'} → Ren Γ Γ' → Sem Γ' T

  GExpS : ∀{n Δ Δ'} → Ctx Δ → Type (suc n) Δ' → TSubn n Δ' Δ → Set
  GExpS Γ T sub = ∀{Γ'} → Ren Γ Γ' → SemS Γ' T sub

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub {Δ} Γ₁ Γ₂ = ∀{n T} → InCtx {n} Γ₁ T → GExp _ Γ₂ T

{-

Heres an idea. If I can get this far without lemmas, then is it possible to finish
without lemmas? If I can prove that the Sem above is equivalent to the
obvious but non-terminating Sem which subst in place in ⋁ case, then
maybe that will work?

e.g. the following Sem2 and GExp2.

e.g. prove that

Sem Γ (⋁ T) = (X : Type n Δ) → Sem Γ (subTypen (append1sub idSubn X) T)
well can't prove =, maybe ∼ or iff

-}

⋁thm : ∀{n Δ Γ T X} → Sem {suc n} {Δ} Γ (⋁ T) → Sem Γ (subTypen (append1subn idSubn X) T)
⋁thm = {!   !}

-- mutual
--   Sem2 : ∀{n Δ} → (Γ : Ctx Δ) → (T : Type n Δ) → Set
--   Sem2 Γ (Var x) = Nf _ Γ (Var x)
--   Sem2 Γ (A ⇒ B) = GExp2 _ Γ A → Sem2 Γ B
--   Sem2 {suc n} {Δ} Γ (⋁ T) = (X : Type n Δ) → Sem2 Γ (subTypen (append1subn idSubn X) T)
--   Sem2 Γ (cumu T) = Sem2 Γ T
--
--   GExp2 : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set
--   GExp2 Δ Γ T = ∀{Γ'} → Ren Γ Γ' → Sem2 Γ' T

mutual
  nApp0 : ∀{Δ Γ T} → Ne {0} Δ Γ T → Sem Γ T
  nApp0 {_} {_} {Var x} e = ne e
  nApp0 {_} {_} {A ⇒ B} e = λ g → nApp0 (app e (reify0 g))

  nAppS : ∀{n Δ Δ' Γ} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → Ne {suc n} Δ Γ (subTypen sub T) → SemS Γ T sub
  nAppS (Var x) sub e = ne e -- prove applySub doesn't affect lower level...
  nAppS (A ⇒ B) sub e = λ g → nAppS B sub (app e (reifyS A sub g))
  nAppS (⋁ T) sub e = λ X → nAppS T (nextn sub X)
    (subst (λ T → Ne _ _ T) (bigLemma [] T) (Ne.TApp e X))
  nAppS {n} {_} {_} {Γ} (cumu T) sub e
    -- = subst (λ T → Sem Γ T) (sym (idSubnFact {_} {_} {_} {subTypen sub T})) (nApp {suc n} _ e)
    = {! e  !}

  nApp : ∀{n Δ Γ} → (T : Type n Δ) → Ne {n} Δ Γ T → Sem Γ T
  nApp {zero} T = nApp0
  nApp {suc n} T e
    = nAppS {n} T idSubn (subst (λ T → Ne _ _ T) (idSubnFact {_} {_} {_} {T}) e)

  reify0 : ∀{Δ Γ T} → GExp {0} Δ Γ T → Nf Δ Γ T
  reify0 {_} {_} {Var x} g = g idRen
  reify0 {_} {_} {A ⇒ B} g = lambda (reify0 λ ren → g (forget1ren ren) λ ren₂ → nApp0 (var (ren₂ (ren same))))

  reifyS : ∀{n Δ Δ' Γ} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → GExpS {n} Γ T sub → Nf Δ Γ (subTypen sub T)
  reifyS (Var x) sub g = g idRen
  reifyS (A ⇒ B) sub g = lambda ((reifyS B sub λ ren → g (forget1ren ren) λ ren₂ → nAppS A sub (var (ren₂ (ren same)))))
  reifyS (⋁ T) sub g = Tlambda {!   !}
  reifyS (cumu T) sub g = {!   !}
