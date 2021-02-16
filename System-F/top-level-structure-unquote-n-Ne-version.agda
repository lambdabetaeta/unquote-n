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

idTRen : ∀{Δ} → TRen Δ Δ
idTRen same = same
idTRen (next x) = next (idTRen x)

forget1Tren : ∀{Δ₁ Δ₂} → (n : ℕ) → TRen (Δ₁ , n) Δ₂ → TRen Δ₁ Δ₂
forget1Tren _ ren x = ren (next x)

weaken1Δ : ∀{Δ n} → TRen Δ (Δ , n)
weaken1Δ ren = next ren

liftTRen : ∀{Δ₁ Δ₂ n} → TRen Δ₁ Δ₂ → TRen (Δ₁ , n) (Δ₂ , n)
liftTRen ren same = same
liftTRen ren (next itc) = next (ren itc)

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

-- can make these easy to prove using other version of rens and subs.
-- actually, just use version where idRen is a constructor so its definitional?
-- keep in mind that later we use ∘ and transSR.
idRenFactType : ∀{n Δ} → (A : Type n Δ) → renType idTRen A ≡ A
idRenFactType = {!   !}

idRenFactΓ : ∀{Δ} → (Γ : Ctx Δ) → renΓ idTRen Γ ≡ Γ
idRenFactΓ = {!   !}

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

-- renΓ : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
TrenICX : ∀{n Δ₁ Δ₂ Γ T} → (ren : TRen Δ₁ Δ₂) → InCtx {n} {Δ₁} Γ T
  → InCtx {n} {Δ₂} (renΓ ren Γ) (renType ren T)
TrenICX ren same = same
TrenICX ren (next x) = next (TrenICX ren x)

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
  cumu : ∀{n Δ Γ T}
    → Exp {suc n} Δ Γ (cumu T) → Exp {n} Δ Γ T

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

  data Ne : ∀{n} → (Δ : TCtx) → Ctx Δ → Type n Δ → Set where
    var : ∀{n Δ Γ T} → InCtx {n} {Δ} Γ T → Ne Δ Γ T
    app : ∀{n Δ Γ A B} → Ne {n} Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B
    TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
      → Ne Δ Γ (⋁ T)
      → (X : Type n Δ)
      → Ne Δ Γ (subTypen (append1subn idSubn X) T)
    cumu : ∀{n Δ Γ T}
      → Ne {suc n} Δ Γ (cumu T) → Ne {n} Δ Γ T

-- ∀₀ X . cumu (X → X)               works
-- ∀₀ X . (cumu X) → (cumu X)        to apply this, would need something of type cumu T
-- ∀­₀ X . cumu X                     works
-- ∀₁ X . ∀₀ Y . (X → Y) → (X → Y)   I can't even write this type?
-- ∀₁ X . ∀₁ Y . (X → Y) → (X → Y)   Why not just write this instead?

--                              T         ↓ outputN    ↓ output type
  data Args : ∀{n Δ} → Ctx Δ → Type n Δ → (nOut : ℕ) → Type nOut Δ  → Set where
    none : ∀{n Δ Γ T} → Args {n} {Δ} Γ T n T
    one : ∀{n Δ Γ A B nOut TOut} → Args Γ B nOut TOut
      → Nf {n} Δ Γ A
      → Args {n} {Δ} Γ (A ⇒ B) nOut TOut
    One : ∀{n Δ Γ nOut TOut} → {T : Type (suc n) (Δ , n)} → (X : Type n Δ)
      → Args {suc n} {Δ} Γ (subTypen (append1subn idSubn X) T) nOut TOut
      → Args {suc n} {Δ} Γ (⋁ T) nOut TOut

    cumu : ∀{n Δ Γ T nOut TOut}
      → Args {n} {Δ} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut

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

TrenMatch : ∀{n Δ₁ Δ₂ T T'} → (ren : TRen Δ₁ Δ₂)
  → Match {n} {Δ₁} T T' → Match (renType ren T) T'
TrenMatch ren (Var x) = Var (ren x)
TrenMatch ren (mA ⇒ mB) = TrenMatch ren mA ⇒ TrenMatch ren mB
TrenMatch ren (⋁ m) = ⋁ (TrenMatch (liftTRen ren) m)
TrenMatch ren (cumu T) = cumu (renType ren T)

-- note, in case I need later, that renMatch using Ren could also work easily
-- because TypeTLS doesn't store variables!

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
  -- idea is that T' : TypeTLS and m : Match T T' arguments are extra, they are only
  -- there for termination purposes. We really only care about T arg, which can
  -- be subststituted because the T' takes care of termination.

  PUExp : ∀{n Δ nOut TOut} → (Γ : Ctx Δ) → (T : Type n Δ) → (T' : TypeTLS)
    → Match T T' → Args Γ T nOut TOut  → Set
  PUExp Γ T T' m none = Nf _ Γ T
  -- why does it know the Var case is unreachable?
  -- PUExp Γ .(Var x) .Var (Var x) args = Nf _ Γ (Var x) -- can prove args = none
  -- TODO TODO TODO: hold up, e argument isn't even used here!!!!!!!!!
  PUExp Γ (A ⇒ B) (A' ⇒ B') (mA ⇒ mB) (one args e) = GExp _ Γ A A' mA → PUExp Γ B B' mB args
  PUExp {suc n} {Δ} Γ (⋁ T) (⋁ T') (⋁ m) (One X args)
    = PUExp Γ (subTypen (append1subn idSubn X) T) T' (subMatch m _ lemma1) args
  PUExp Γ .(cumu T) .cumu (cumu T) (cumu args) = PUExp Γ T (getTLS T) (getTLSMatch T) args

  -- -- Exp that can be partially unquoted to any amount
  APUExp : ∀{n} → (Δ : TCtx) → Ctx Δ → (T : Type n Δ)
    (T' : TypeTLS) → Match T T' → Set
  APUExp Δ Γ T T' m = ∀{nOut TOut} → (args : Args Γ T nOut TOut) → PUExp Γ T T' m args

  -- -- Exp that can be in a weaker context AND partially unquoted
  GExp : ∀{n} → (Δ : TCtx) → Ctx Δ → (T : Type n Δ)
    (T' : TypeTLS) → Match T T' → Set
  GExp Δ Γ T T' m = ∀{Δ' Γ'} → (tren : TRen Δ Δ') → Ren (renΓ tren Γ) Γ'
    → APUExp {_} Δ' Γ' (renType tren T) T' (TrenMatch tren m)

nApp : ∀{n Δ Γ T T' nOut TOut} → (m : Match T T') → (args : Args {n} {Δ} Γ T nOut TOut)
  → Ne Δ Γ T → PUExp Γ T T' m args
nApp m none e = ne e
nApp {_} {_} {Γ} {A ⇒ B} (mA ⇒ mB) (one args x) e
  = λ x → nApp mB args (app e let res = x idTRen idRen none
      in let res₁ = subst (λ A → Nf _ _ A) (idRenFactType A) res
      in subst (λ Γ → Nf _ Γ _) (idRenFactΓ Γ) res₁ )
nApp (⋁ m) (One X args) e
  = nApp (subMatch m (append1subn idSubn X) lemma1) args (TApp e X)
nApp (cumu T) (cumu args) e = nApp (getTLSMatch T) args (cumu e) -- I don't know how this case works, I was just playing proof golf. Look at later.

-- IDEA: Ctx, TLSCtx, and MatchCtx
-- the TLSCtx is just a list of TypeTLS, and then the MatchCtx is a match for
-- each type from Ctx and TLS from TLSCtx.

data TLSCtx : Set where
  ∅ : TLSCtx
  _,_ : TLSCtx → TypeTLS → TLSCtx

data MatchCtx : ∀{Δ} → Ctx Δ → TLSCtx → Set where
  ∅ : ∀{Δ} → MatchCtx {Δ} ∅ ∅
  _,_ : ∀{n Δ Γ Γ' T'} → {T : Type n Δ}
    → MatchCtx {Δ} Γ Γ' → Match T T' → MatchCtx (Γ , T) (Γ' , T')

getTLSfromICX : ∀{Δ n T} → {Γ : Ctx Δ} → (Γ' : TLSCtx) → MatchCtx Γ Γ'
  → InCtx {n} Γ T → TypeTLS
getTLSfromICX (Γ' , T') (Γm , m) same = T'
getTLSfromICX (Γ' , T') (Γm , m) (next x) = getTLSfromICX Γ' Γm x

getMatchfromICX : ∀{Δ n T} → {Γ : Ctx Δ} → (Γ' : TLSCtx) → (m : MatchCtx Γ Γ')
  → (x : InCtx {n} Γ T) → Match T (getTLSfromICX Γ' m x)
getMatchfromICX (Γ' , T') (Γm , m) same = m
getMatchfromICX (Γ' , T') (Γm , m) (next x) = getMatchfromICX Γ' Γm x

Sub : ∀{Δ} → (Γ₁ : Ctx Δ) → (Γ₁' : TLSCtx) → MatchCtx Γ₁ Γ₁'
  → (Γ₂ : Ctx Δ) → (Γ₂' : TLSCtx) → MatchCtx Γ₁ Γ₁' → Set
Sub Γ₁ Γ₁' Γm₁ Γ₂ Γ₂' Γm₂ = ∀{n T} → (x : InCtx {n} Γ₁ T)
  → GExp _ Γ₂ T (getTLSfromICX Γ₁' Γm₁ x) (getMatchfromICX Γ₁' Γm₁ x)

idSub : ∀{Δ Γ Γ' Γm} → Sub {Δ} Γ Γ' Γm Γ Γ' Γm
idSub {_} {Γ} {Γ'} {Γm} {n} {T} x tren ren args
  = nApp (TrenMatch tren (getMatchfromICX Γ' Γm  x)) args (var (ren (TrenICX tren x)))

liftSub : ∀{Δ Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂ n} → {T : Type n Δ}
  → Sub {Δ} Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂ → ∀{T' m}
  → Sub (Γ₁ , T) (Γ'₁ , T') (Γm₁ , m) (Γ₂ , T) (Γ'₁ , T') (Γm₂ , m)
liftSub sub {T'} {m} same tren ren args
  = nApp (TrenMatch tren m) args (var (ren same))
liftSub sub (next x) tren ren args = sub x tren (forget1ren ren) args

_∘_ : ∀{Δ A B C} → Ren {Δ} A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

-- TODO: come back to this when implementing unquote-n
-- transSR : ∀{Δ Γ₁ Γ₂ Γ₃} → Sub {Δ} Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
-- -- transSR sub ren x ren₂ = sub x (ren ∘ ren₂)
-- transSR sub ren x tren ren₂ = sub x tren {! ren ∘ ren₂  !} {!   !}

append1sub : ∀{n Δ Γ₁ Γ'₁ Γm₁ A A' m Γ₂ Γ'₂ Γm₂}
  → Sub {Δ} Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂
  → GExp {n} Δ Γ₂ A A' m
  → Sub (Γ₁ , A) (Γ'₁ , A') (Γm₁ , m) (Γ₂ , A) (Γ'₂ , A') (Γm₂ , m)
append1sub sub e same tren ren args = e tren (forget1ren ren) args
append1sub sub e (next x) tren ren args = sub x tren (forget1ren ren) args

unquote-n : ∀{n Δ Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂ T}
-- unquote-n : ∀{n Δ Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂ T T' Tm}
  → Exp {n} Δ Γ₁ T → Sub Γ₁ Γ'₁ Γm₁ Γ₂ Γ'₂ Γm₂
  → APUExp Δ Γ₂ T (getTLS T) (getTLSMatch T)
  -- → APUExp Δ Γ₂ T T' Tm
  -- TODO: should we have getTLS and getTLSMatch here?
unquote-n (var x) sub = {! λ args → sub x idTRen idRen  !}
unquote-n (lambda e) sub none = {!   !}
  -- = lambda (unquote-n e (liftSub sub) none)
unquote-n (lambda e) sub (one args x) = {!   !}
unquote-n (app e₁ e₂) sub args
  = unquote-n e₁ sub (one args ?) {! λ ren₁  !} -- (unquote-n e₂ sub none)
unquote-n (Tlambda e) sub args = {!   !}
unquote-n (TApp e X) sub args = {!   !}
unquote-n (cumu e) sub args = {!   !}

{-
Things to figure out:
-- exactly what should really be parametrized by TypeTLS, TLSCtx, Match, and MatchCtx
    out of the various functions above?
-- what is going on with var case?
-- why does arg in app case have type Nf instead of APUExp?
-}
