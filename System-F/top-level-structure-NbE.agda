open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)
open import Data.List
open import Data.Empty
open import Relation.Nullary

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

forget1Tren : ∀{Δ₁ Δ₂} → (n : ℕ) → TRen (Δ₁ , n) Δ₂ → TRen Δ₁ Δ₂
forget1Tren _ ren x = ren (next x)

-- represents a type at level l
data Type : ℕ → TCtx →  Set where
  Var : ∀{Δ n} → InTCtx Δ n → Type n Δ
  _⇒_ : ∀{n Δ} → Type n Δ → Type n Δ → Type n Δ
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

-- TLS = top level structure
data TypeTLS : Set where
  -- TODO: should I store the InTCtx in the Var case? do I need it?
  Var : TypeTLS
  _⇒_ : TypeTLS → TypeTLS → TypeTLS
  ⋁ : TypeTLS → TypeTLS
  -- cumu takes no arguments because anything under it is not top level structure!
  cumu : TypeTLS

data Match : ∀{n Δ} → Type n Δ → TypeTLS → Set where
  Var : ∀{Δ n} → (x : InTCtx Δ n) → Match (Var x) Var
  _⇒_ : ∀{n Δ A' B'} → {A : Type n Δ} → {B : Type n Δ}
    → Match A A' → Match B B' → Match (A ⇒ B) (A' ⇒ B')
  ⋁ : ∀{n Δ T'} → {T : Type (suc n) (Δ , n)}
    → Match T T' → Match (⋁ T) (⋁ T')
  cumu : ∀{n Δ} → (T : Type n Δ) → Match (cumu T) cumu

getTLS : ∀{n Δ} → Type n Δ → TypeTLS
getTLS (Var x) = Var
getTLS (A ⇒ B) = getTLS A ⇒ getTLS B
getTLS (⋁ T) = ⋁ (getTLS T)
getTLS (cumu T) = cumu

getTLSMatch : ∀{n Δ} → (T : Type n Δ) → Match T (getTLS T)
getTLSMatch (Var x) = Var x
getTLSMatch (A ⇒ B) = getTLSMatch A ⇒ getTLSMatch B
getTLSMatch (⋁ T) = ⋁ (getTLSMatch T)
getTLSMatch (cumu T) = cumu T

applyNM : ∀{n m Δ₁ Δ₂} → (x : InTCtx Δ₁ n)
  → (sub : TSubn m Δ₁ Δ₂) → ¬ (n ≡ m) → InTCtx Δ₂ n
applyNM same (nextn sub x) p = ⊥-elim (p refl)
applyNM same (nextm sub) p = same
applyNM (next x) (nextn sub X) p = applyNM x sub p
applyNM (next x) (nextm sub) p = next (applyNM x sub p)

applyVarFact : ∀{n m Δ₁ Δ₂} → (x : InTCtx Δ₁ n)
  → (sub : TSubn m Δ₁ Δ₂) → (p : ¬ (n ≡ m))
  → applySub sub x ≡ Var (applyNM x sub p)
applyVarFact same (nextn sub x) p = ⊥-elim (p refl)
applyVarFact same (nextm sub) p = refl
applyVarFact (next x) (nextn sub X) p = applyVarFact x sub p
applyVarFact (next x) (nextm sub) p = cong (renType weaken1Δ) (applyVarFact x sub p)

subMatch : ∀{n m Δ₁ Δ₂ T'} → {T : Type m Δ₁} → Match T T'
  → (sub : TSubn n Δ₁ Δ₂) → ¬ (m ≡ n)
  → Match (subTypen sub T) T'
subMatch (Var x) sub p = subst (λ T → Match T Var) (sym (applyVarFact x sub p)) (Match.Var _)
subMatch (mA ⇒ mB) sub p = subMatch mA sub p ⇒ subMatch mB sub p
subMatch (⋁ m) sub p = ⋁ (subMatch m (liftTSubn sub) p)
subMatch (cumu T) sub p = cumu (subTypen sub T)

-- surely this is not the easiest way to prove 0 ≠ 1 in agda?
lemma2 : ¬ (⊤ ≡ ⊥)
lemma2 p = subst (λ T → T) p tt

helper : ℕ → Set
helper 0 = ⊤
helper (suc n) = ⊥

helper2 : ℕ → ℕ
helper2 0 = 0
helper2 (suc n) = n

lemma1 : {n : ℕ} → ¬ (suc n ≡ n)
lemma1 {zero} p = lemma2 (sym (cong helper p))
lemma1 {suc n} p = lemma1 {n} (cong helper2 p)

mutual
  -- by induction on first n, and then tls
  Sem : ∀{n Δ} → (Γ : Ctx Δ) → (T : Type n Δ) → (tls : TypeTLS)
    → Match T tls → Set
  Sem Γ .(Var x) .Var (Var x) = Nf _ Γ (Var x)
  Sem Γ (A ⇒ B) (A' ⇒ B') (mA ⇒ mB) = GExp _ Γ A A' mA → Sem Γ B B' mB
  Sem {suc n} {Δ} Γ (⋁ T) (⋁ T') (⋁ mT)
    = (X : Type n Δ) → Sem Γ (subTypen (append1subn idSubn X) T) T'
    (subMatch mT (append1subn idSubn X) lemma1)
  Sem Γ .(cumu T) .cumu (cumu T) = Sem Γ T (getTLS T) (getTLSMatch T)

  GExp : ∀{n} → (Δ : TCtx) → Ctx Δ → (T : Type n Δ)
    (T' : TypeTLS) → Match T T' → Set
  GExp Δ Γ T T' m = ∀{Γ'} → Ren Γ Γ' → Sem Γ' T T' m

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub Γ₁ Γ₂ = ∀{n T} → InCtx {n} Γ₁ T → GExp _ Γ₂ T (getTLS T) (getTLSMatch T)

mutual
  nApp : ∀{n Δ Γ T'} → {T : Type n Δ} → (m : Match T T')
    → Ne Δ Γ T → Sem Γ T T' m
    -- TODO: might want to return GExp instead!
  nApp (Var x) e = ne e
  nApp (mA ⇒ mB) e = λ g → nApp mB (app e (reify mA g))
  nApp (⋁ m) e = λ X → nApp (subMatch m (append1subn idSubn X) lemma1) (Ne.TApp e X)
  nApp {_} {_} {_} {cumu} {cumu T} (cumu mT) e = nApp (getTLSMatch T) {! e  !}

  {-
  I think that this difficulty here exposes a larger problem:
  There is no way to apply a cumu to arguments!!!!
  if id : ⋁ cumu (Var same ⇒ Var same)
  then there is no way to apply (id T t)
  -}

  reify : ∀{n Δ Γ T T'} → (m : Match T T') → GExp {n} Δ Γ T T' m → Nf Δ Γ T
  reify (Var x) g = g idRen
  -- reify (A ⇒ B) g = λ x . reify (g x)
  reify (mA ⇒ mB) g = lambda (reify mB λ ren → g (forget1ren ren) λ ren₂ → nApp mA (var (ren₂ (ren same))))
  -- reify (∀ X . A) g = Λ X . reify (g X)
  reify {suc n} {Δ} {Γ} {⋁ T} {⋁ T'} (⋁ m) g
    -- = Tlambda (reify {suc n} {Δ , n} m λ ren → let a = g {!    !} {!   !} in {! g idRen ?  !} )
    = Tlambda let a = g {!   !} {! Ne.var {_} {Δ , n} same  !} in {!   !}
    -- IDEA: in TCtx (Δ , n), (Var same) is a Type n (Δ n). But, I want it to be
    -- a Type n Δ.  In fact, thats what it is, just not how Var constructor of Type works.
    -- Given (X : Type n Δ), can get a sub : TSub (Δ , n) Δ
    -- g : (X : Type n Δ) → Sem Γ (T [0 / X])
    -- SOLUTION IS putting TRen in Sub, because without rens in Sub,
    -- g outputs into Sem Δ Γ ?, which wouldn't work in lambda case either!
  reify (cumu T) g = {!   !}

  {-
  I have no idea how to do Tlambda case. I should either think of intuition, or
  just do unquote-n, because I'm more familiar with it.
  Presumably there should be a TApp somewhere to match the (append1subn idSUbn X)
    that comes from Sem ⋁ case.

  In unquote-n STLC, we have Γ sub. So maybe here we additionally need TSub,
  and in TLambda case, we append to that.
  IDEA IDEA IDEA: seems very relevant to ⋁ case of reify.
  -}
