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

data TCtx : Set where
  ∅ : TCtx
  _,_ : TCtx → ℕ → TCtx


-- represents a type at level l
data Type : ℕ → TCtx →  Set where
  EndCtx : ∀{Δ n} → Type n (Δ , n)
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
  ⋁ : ∀{n Δ} → Type (suc n) (Δ , n) → Type (suc n) Δ
  cumu : ∀{n Δ} → Type n Δ → Type (suc n) Δ
  weakenΔ : ∀{Δ n m} → Type n Δ → Type n (Δ , m)

data Ctx : Set where
  ∅ : Ctx
  _,_ : ∀{n Δ} → Ctx → Type n Δ → Ctx

data InCtx : ∀{n Δ} → (Γ : Ctx) → Type n Δ → Set where
  same : ∀{n Δ Γ T} → InCtx {n} {Δ} (Γ , T) T
  next : ∀{n m Δ Γ A} → {T : Type m Δ}
    → InCtx {n} {Δ} Γ A → InCtx (Γ , T) A


subCtx : ∀{n Δ Γ T} → (icx : InCtx {n} {Δ} Γ T) → Ctx
subCtx (same {_} {_} {Γ}) =  Γ
subCtx (next {_} {_} {_} {_} {_} {T} icx) = subCtx icx , T

-- nothing means use toSub, just means just adjust x for new context.
varSub : ∀{Δ Γ n A B} → (icx : InCtx {n} {Δ} Γ A)
  → (x : InCtx Γ B) → (B ≡ A) ⊎ (InCtx (subCtx icx) B)
varSub same same = inj₁ refl
varSub same (next x) = inj₂ x
varSub (next icx) same = inj₂ same
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ x' = inj₂ (next x')

data TSubn : ℕ → TCtx → TCtx → Set where
  ∅ : ∀{n} → TSubn n ∅ ∅
  nextn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
  -- nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → InTCtx Δ₂ m → TSubn n (Δ₁ , m) Δ₂
  -- TODO: think later about old vs new design here. Which makes things more definitionally true?
  nextm : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , m) (Δ₂ , m)

liftTSubn : ∀{n l Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → TSubn n (Δ₁ , l) (Δ₂ , l)
liftTSubn = nextm

-- TODO: delete this
append1subn : ∀{n Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type n Δ₂ → TSubn n (Δ₁ , n) Δ₂
append1subn = nextn

idSubn : ∀{n Δ} → TSubn n Δ Δ
idSubn {n} {∅} = ∅
idSubn {n} {Δ , x} = nextm idSubn

subTypen : ∀{n m Δ₁ Δ₂} → TSubn n Δ₁ Δ₂ → Type m Δ₁ → Type m Δ₂
subTypen sub (A ⇒ B) = subTypen sub A ⇒ subTypen sub B
subTypen sub (⋁ T)
  = ⋁ (subTypen (liftTSubn sub) T)
subTypen sub (cumu T) = cumu (subTypen sub T)
  -- IF THESE ARE CORRECT, IT IS SCARY HOW WELL THESE TSUBS AND WEAKENINGS GO TOGETHER
subTypen (nextn sub X) EndCtx = X
subTypen (nextm sub) EndCtx = EndCtx
subTypen (nextn sub X) (weakenΔ T) = subTypen sub T
subTypen (nextm sub) (weakenΔ T) = weakenΔ (subTypen sub T)

data Exp : ∀{n} → (Δ : TCtx) → Ctx → Type n Δ → Set where
  lambda : ∀{n Δ Γ A B} → Exp {n} Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  app : ∀{n Δ Γ A B} → Exp {n} Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Tlambda : ∀{Δ n Γ T}
    → Exp (Δ , n) Γ T → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subTypen (append1subn idSubn X) T)
  EndCtx : ∀{n Δ Γ T} → Exp {n} Δ (Γ , T) T
  cumu : ∀{Δ n T Γ}
    → Exp {n} Δ Γ T
    → Exp {suc n} Δ Γ (cumu T)
  weakenΔ : ∀{n Δ Γ T m} → Exp {n} Δ Γ T → Exp {n} (Δ , m) Γ (weakenΔ T)
  weakenΓ : ∀{n Δ Γ T nA ΔA} → {A : Type nA ΔA} → Exp {n} Δ Γ T → Exp Δ (Γ , A) T

-- Test if this form of variables and contexts actually works, implement function
-- ∀ X ∀ Y → (X → Y) → X → Y
-- what if I put cumu and weakenΔ's in different orderings and locations?
idType : Type 1 ∅
idType = ⋁ (⋁ ((cumu (weakenΔ EndCtx) ⇒ cumu EndCtx ) ⇒ (cumu (weakenΔ EndCtx) ⇒ cumu EndCtx)))

id : Exp ∅ ∅ idType
id = Tlambda (Tlambda (lambda (lambda (app (weakenΓ EndCtx) EndCtx))))

-- Although this is a wierd representation, if in fact I can really correctly write
-- and program, and the ordering of cumu and weakenΔ and weakenΓ really doesn't matter
-- after eta expansion, then it should be theoretically possible to define normalization.
-- I mean, why not?

-- The thing that seems dubious about weakenΔ and weakenΓ is an InCtx based sub, like subNf.
--    Maybe it will work by the two cases will be next and same of InCtx correspond to where EndCtx
--    Is the var being subbed for or another var, like what varSub does
--    And for (weakenΓ e), if same then just return rest unsubbed as that var no longer relevant
--        and if (next x), then just recurse on x and e
-- The thing that seems dubious about having Γ not parametrized by Δ is what if a given
-- type in Γ is at the wrong Δ? If I want an element of Exp 0 (Δ , n) (Type 0 Δ)
-- can I get it?
-- weakenΔ (EndCtx)     works right?
-- So can't have Ctx not parametrized by TCtx unless weakenΔ exists.

-- On the other hand, could reintroduce InCtx (not InTCtx) if I wanted, as weakenΓ
-- isn't part of that story.
{-


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
  appNf0 (A ⇒ B) (lambda e) (one args a)
    = appNf0 B (subNf same a e) args
  appNf0 T (ne x args₁) (one a args₂) = {!   !}
  appNf0 T e none = e
  appNfS : ∀{n Δ Δ' Γ nOut TOut} → (T : Type (suc n) Δ') → (sub : TSubn n Δ' Δ)
    → Nf {suc n} Δ Γ (subTypen sub T) -- Tsubbed
    → (args : Args Γ (subTypen sub T) nOut TOut) -- Tsubbed)
    → Nf Δ Γ TOut
    -- crucial idea: we are doing induction on T, not e.

  appNfS (Var X) sub e args = {!   !} -- really just have to prove sub X = X, so args = 0.
  appNfS (A ⇒ B) sub (lambda e) (one args a)
    = appNfS B sub (subNf same a e) args
  appNfS (⋁ T) sub (Tlambda e) (One X args)
    = appNfS T (append1subn sub X) (let e' = subNfTSubn (append1subn idSubn X) e
      in {! e'  !} ) -- subRenCancelΓ, and one more thing
      {! args  !}
  appNfS (cumu T) sub (cumu e) (cumu args)
    = appNf (subTypen sub T) e args
  appNfS T sub (ne x args₁) args₂ = {!   !}
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
-}
