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

mutual
  data Context : Set where
    ∅ : Context
    _,_ : ∀{n} → (Γ : Context) → Type n Γ → Context

  data Type : ℕ → Context → Set where
    Π : ∀{n Γ} → (A : Type n Γ) → (Type n (Γ , A)) → Type n Γ
    cumu : ∀{n Γ} → Type n Γ → Type (suc n) Γ -- TODO: redundant with cumu in Nf.
    type : ∀{Γ} → (n : ℕ) → Type (suc n) Γ
    -- Var : ∀{Γ} → (x : InCtx Γ) → Type (suc (levelAt x)) Γ -- PROBLEM : this works for Exp, but not for Type as not all types are type.
    fromE : ∀{Γ n} → Nf Γ (type n) → Type n Γ -- If I ever use this, should be Nf, as even Exps need to use Nf's for types.

  data Pre : Context → Context → Set where
    same : ∀{Γ} → Pre Γ Γ
    next : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₂} → Pre Γ₁ Γ₂ → Pre Γ₁ (Γ₂ , T)

  preCompare : ∀{Γ₁ Γ₂ Γ₃} → (Pre Γ₁ Γ₃) → (Pre Γ₂ Γ₃)
    → (Pre Γ₁ Γ₂ ⊎ Pre Γ₂ Γ₁)
  preCompare same pre₂ = inj₂ pre₂ -- NOTE that there is overlap if both are same.
  preCompare pre₁ same = inj₁ pre₁ -- They actually give the same anwer on overlap.
  preCompare (next pre₁) (next pre₂) = preCompare pre₁ pre₂ -- could resolve with four cases, for all four options.

  --          ↓ ↓    ↓    ↓            ↓   These make the arguments to any weakening function, by specifying how the context is being weakened.
  weakenΓ : ∀{Γ Γpre n} → Pre Γpre Γ → Type n Γpre → Context
  weakenΓ (same {Γ}) T = Γ , T
  weakenΓ (next {_} {_} {_} {T} pre) A = weakenΓ pre A , weakenType pre A T

  weakenType : ∀{Γ Γpre n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → Type m Γ → Type m (weakenΓ pre W)
  weakenType pre W (Π A B) = Π (weakenType pre W A) (weakenType (next pre) W B)
  weakenType pre W (cumu T) = cumu (weakenType pre W T)
  weakenType pre W (type n) = type n
  -- weakenType pre W (Var x) = {!   !}
  weakenType pre W (fromE e) = {!   !}
    -- = Var (let a = weakenICX pre W {! x  !} in  ?) -- Var (weakenICX pre W x)

  weakenTypeByPre : ∀{Γpre Γ n} → Pre Γpre Γ → Type n Γpre → Type n Γ
  weakenTypeByPre same T = T
  weakenTypeByPre (next {_} {_} {_} {W} pre) T
    = weakenType same W (weakenTypeByPre pre T)

  data InCtx : ℕ → Context → Set where
    same : ∀{Γ n} → {T : Type n Γ} → InCtx n (Γ , T)
    next : ∀{Γ n m} → {T : Type n Γ} → InCtx m Γ → InCtx m (Γ , T)

  -- levelAt : ∀{Γ} → InCtx Γ → ℕ
  -- levelAt (same {_} {m}) = m
  -- levelAt (next x) = levelAt x

  ctxAt : ∀{n Γ} → InCtx n Γ → Context
  ctxAt (same {Γ}) = Γ
  ctxAt (next x) = ctxAt x

  typeAt : ∀{n Γ} → (x : InCtx n Γ) → Type n (ctxAt x)
  typeAt (same {_} {_} {T}) = T
  typeAt (next x) = typeAt x

  ICXtoPre : ∀{n Γ} → (x : InCtx n Γ) → Pre (ctxAt x) Γ
  ICXtoPre same = next same
  ICXtoPre (next x) = next (ICXtoPre x)

  weakenICX : ∀{Γ Γpre n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
    → InCtx m Γ → InCtx m (weakenΓ pre W)
  weakenICX same W x = next x
  weakenICX (next pre) W same = same
  weakenICX (next pre) W (next x) = next (weakenICX pre W x)

  -- weakenICXlevel≡ : ∀{Γ Γpre n m} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
  --   → (x : InCtx m Γ)
  --   → levelAt (weakenICX pre W x) ≡ levelAt x
  -- weakenICXlevel≡ same W x = refl
  -- weakenICXlevel≡ (next pre) W same = refl
  -- weakenICXlevel≡ (next pre) W (next x) = weakenICXlevel≡ pre W x

  -- TODO: need to really think about what this is, is pre before or after x, etc.
  -- Type will be complicated.

  -- weakenICXCtx≡ : ∀{Γ Γpre n} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
  --   → (x : InCtx Γ)
  --   → ctxAt (weakenICX pre W x) ≡ weakenΓ pre W (ctxAt x)
  -- weakenICXCtx≡ same W x = refl
  -- -- Something is suspiscious here!!!!!!!!!!!
  -- weakenICXCtx≡ (next pre) W same = {!   !} -- TODO: this is not just hard to prove, but wrong!!!!!!!!!!!!!
  -- weakenICXCtx≡ (next pre) W (next x) = weakenICXCtx≡ pre W x

  -- weakenICXtype≡

  weakenICXcomm : ∀{Γ Γpre n} → (W : Type n Γpre) → (x : InCtx n Γ) → (pre : Pre Γpre Γ)
    → (weakenTypeByPre (ICXtoPre (weakenICX pre W x)) (typeAt (weakenICX pre W x)))
      ≡ weakenType pre W (weakenTypeByPre (ICXtoPre x) (typeAt x))
  weakenICXcomm W x same = refl
  weakenICXcomm W same (next pre) = {!   !}
  weakenICXcomm W (next x) (next pre) = {! weakenICXcomm W x pre  !}


  data Exp : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Exp {n} (Γ , A) B → Exp Γ (Π A B)
    cumu : ∀{Γ n T} → Exp {n} Γ T → Exp {suc n} Γ (cumu T)
    var : ∀{Γ n} → (x : InCtx n Γ) → Exp Γ (weakenTypeByPre (ICXtoPre x) (typeAt x))
    app : ∀{Γ n A B} → Exp {n} Γ (Π A B) → (a : Exp Γ A) → Exp {n} Γ {! subType same a B  !} -- This actually requires normalize.
    fromT : ∀{Γ n} → Type n Γ → Exp Γ (type n) -- needed for e.g. applying id : ∀X . X → X  to a specific type.

  -- Normal form
  data Nf : ∀{n} → (Γ : Context) → Type n Γ → Set where
    lambda : ∀{n Γ A B} → Nf {n} (Γ , A) B → Nf Γ (Π A B)
    cumu : ∀{Γ n T} → Nf {n} Γ T → Nf {suc n} Γ (cumu T)
    fromT : ∀{Γ n} → Type n Γ → Nf Γ (type n)
    -- Neutral form
    ne : ∀{Γ nOut TOut n}
      → (x : InCtx n Γ)
      → (args : Args Γ (weakenTypeByPre (ICXtoPre x) (typeAt x)) nOut TOut)
      → Nf Γ TOut

  subΓ : ∀{Γ n} → (x : InCtx n Γ) → (toSub : Nf (ctxAt x) (typeAt x)) → Context
  subΓ (same {Γ}) toSub = Γ
  subΓ (next {_} {_} {_} {T} x) toSub = subΓ x toSub , subType x toSub T

  -- Unfortunately, due to Agda, the function needs to be in between Nf and Args.
  subType : ∀{Γ n m} → (x : InCtx m Γ) → (toSub : Nf (ctxAt x) (typeAt x))
    → Type n Γ → Type n (subΓ x toSub)
  subType x toSub (Π A B) = Π (subType x toSub A) (subType (next x) toSub B)
  subType x toSub (cumu T) = cumu (subType x toSub T)
  subType x toSub (type n) = type n
  subType x toSub (fromE e) = fromE (subNf x toSub e)

  -- subICX : ∀{Γ}

-- --                              T             ↓ outputN   ↓ output type
  data Args : ∀{n} → (Γ : Context) → Type n Γ → (nOut : ℕ) → Type nOut Γ
    → Set where
    none : ∀{n Γ T} → Args {n} Γ T n T
    one : ∀{n Γ A B nOut TOut}
      → (arg : Nf {n} Γ A)
      → Args Γ (subType same arg B) nOut TOut
      → Args {n} Γ (Π A B) nOut TOut
    cumu : ∀{n Γ T nOut TOut}
      → Args {n} Γ T nOut TOut → Args {suc n} Γ (cumu T) nOut TOut

  -- Hard to implement, do I need it?
  -- weakenNf : ∀{Γ Γpre n m T} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
  --   → Nf {m} Γ T → Nf {m} (weakenΓ pre W) (weakenType pre W T)
  -- weakenNf pre W (lambda e) = lambda (weakenNf (next pre) W e)
  -- weakenNf pre W (cumu e) = cumu (weakenNf pre W e)
  -- weakenNf pre W (fromT T) = fromT (weakenType pre W T)
  -- weakenNf pre W (ne x args)
  --   -- = ne (weakenICX pre W x) (weakenArgs pre W {! args  !})
  --   = ne (weakenICX pre W x) {! weakenArgs pre W args  !}

  -- weakenArgs : ∀{Γ Γpre n m T nOut TOut} → (pre : Pre Γpre Γ) → (W : Type n Γpre)
  --   → Args {m} Γ T nOut TOut
  --   → Args {m} (weakenΓ pre W) (weakenType pre W T) nOut (weakenType pre W TOut)
  -- weakenArgs = {!   !}

  -- -- TODO TODO TODO: this doesn't actually use the n anywhere!!!!!!!!
  -- data Subn : ℕ → Context → Context → Set where
  --   idSub : ∀{n Γ} → Subn n Γ Γ
  --   -- TODO which way around should _,_ go out of the two options here?
  --   cons : ∀{n Γ₁ Γ₂ m} → Subn n Γ₁ Γ₂ → (x : InCtx m Γ₂) → (toSub : Nf (ctxAt x) (typeAt x))
  --     → Subn n Γ₁ (subΓ x toSub)
  --   -- _,_ : ∀{n Γ₁ Γ₂} → (x : InCtx Γ₁) → (toSub : Nf (ctxAt x) (typeAt x))
  --     -- → Subn n (subΓ x toSub) Γ₂ → Subn n Γ₁ Γ₂
  --
  -- subnType : ∀{Γ₁ Γ₂ n m} → Subn n Γ₁ Γ₂ → Type m Γ₁ → Type m Γ₂
  -- subnType idSub T = T
  -- subnType (cons sub x toSub) T = subType x toSub (subnType sub T)

  data TSubn : ℕ → Context → Context → Set where
    ∅ : ∀{n} → TSubn n ∅ ∅
    nextn : ∀{n m Γ₁ Γ₂ T} → (sub : TSubn n Γ₁ Γ₂)
      → Nf {m} Γ₂ (subAllType sub T) → TSubn n (Γ₁ , T) Γ₂
    nextm : ∀{n m Γ₁ Γ₂} → {T : Type m Γ₁} → (sub : TSubn n Γ₁ Γ₂)
      → TSubn n (Γ₁ , T) (Γ₂ , subAllType sub T)

  subAllType : ∀{n m Γ₁ Γ₂} → TSubn n Γ₁ Γ₂ → Type m Γ₁ → Type m Γ₂
  subAllType sub (Π A B) = Π (subAllType sub A) (subAllType (nextm sub) B)
  subAllType sub (cumu T) = cumu (subAllType sub T)
  subAllType sub (type n) = type n
  subAllType sub (fromE e) = fromE (subAllNf sub e)

  subAllNf : ∀{Γ₁ Γ₂ n m} → {T : Type m Γ₁} → (sub : TSubn n Γ₁ Γ₂)
    → Nf Γ₁ T → Nf Γ₂ (subAllType sub T)
  subAllNf sub (lambda e) = lambda (subAllNf (nextm sub) e)
  subAllNf sub (cumu e) = cumu (subAllNf sub e)
  subAllNf sub (fromT x) = fromT (subAllType sub x)
  subAllNf sub (ne x args) = {!   !}

  idSubn : ∀{n Γ} → TSubn n Γ Γ
  idSubn {n} {∅} = ∅
  idSubn {n} {Γ , A} = {!   !} -- subst (λ T → TSubn n (Γ , A)  (Γ , T)) idSubnFact (nextm idSubn) -- nextm idSubn

  -- idSubnApplyFact : ∀{n m Δ x} → Var x ≡ applySub {n} {m} (idSubn {n} {Δ}) x
  -- idSubnApplyFact {_} {_} {_} {same} = refl
  -- idSubnApplyFact {_} {_} {_} {next x} = cong (renType weaken1Δ) idSubnApplyFact

  idSubnFact : ∀{n m Γ T} → subAllType {n} {m} {Γ} {Γ} idSubn T ≡ T
  idSubnFact = {!   !}

  -- IDEA: do I need subNfImpl, or can I just use subNf?
  -- subNfImpl : ∀{n k Γ Γ' T m} → (x : InCtx m Γ) → (sub : Subn n Γ' Γ)
  --   → (toSub : Nf (ctxAt x) (typeAt x))
  --   → Nf {k} Γ (subnType sub T)
  --   → Nf (subΓ x toSub) (subType x toSub (subnType sub T)) -- TODO: unsure about order of subs here
  -- subNfImpl x sub toSub e = {! e  !}

  appNf : ∀{n Γ nOut TOut} → (T : Type n Γ)
    → Nf {n} Γ T
    → (args : Args Γ T nOut TOut)
    → Nf Γ TOut
  appNf {zero} T e count = appNf0 T e count
  appNf {suc n} T e count = appNfS T {! idSubn  !} {!   !} {!   !}

  subNf : ∀{n Γ T m} → (x : InCtx m Γ) -- TODO: maybe can just implement this in terms of subAllNf
    → (toSub : Nf (ctxAt x) (typeAt x))
    → Nf {n} Γ T → Nf (subΓ x toSub) (subType x toSub T)
  subNf x toSub (lambda e) = lambda (subNf (next x) toSub e)
  subNf x toSub (cumu e) = cumu (subNf x toSub e)
  subNf x toSub (fromT T) = fromT (subType x toSub T)
  subNf x toSub (ne x₁ args) = {!   !} -- with varSub x toSub x₁


  appNf0 : ∀{Γ nOut TOut} → (T : Type 0 Γ)
    → Nf {0} Γ T
    → (count : Args Γ T nOut TOut)
    → Nf Γ TOut
  appNf0 (Π A B) (lambda e) (one arg args)
    = appNf0 (subType same arg B) (subNf same arg e) args
  appNf0 T (ne x args) (one arg count) = {!   !}
  appNf0 T e none = e

  appNfS : ∀{n Γ Γ' nOut TOut} → (T : Type (suc n) Γ') → (sub : TSubn n Γ' Γ)
    → Nf {suc n} Γ (subAllType sub T) -- Tsubbed
    → (args : Args Γ (subAllType sub T) nOut TOut) -- Tsubbed)
    → Nf Γ TOut
  appNfS (Π A B) sub (lambda e) (one arg args)
    = appNfS B (nextn sub arg) {!  subNf same arg e !} {!args   !}
  appNfS (cumu T) sub (cumu e) (cumu args) = appNf (subAllType sub T) e args
  appNfS T sub (ne x args₁) args₂ = {!   !}
  appNfS T sub e none = e

-- ΠsubnType≡ : ∀{n Γ₁ Γ₂} → (sub : Subn n Γ₁ Γ₂) → {A : Type (suc n) Γ₁}
--   → {B : Type (suc n) (Γ₁ , A)}
--   → subnType sub (Π A B) ≡ Π (subnType sub A) {!   !} -- (subnType {! nextm sub  !} B)
-- ΠsubnType≡ = {!   !}
--
-- appNfSOtherSubs : ∀{n Γ Γ' nOut TOut} → (T : Type (suc n) Γ') → (sub : Subn n Γ' Γ)
--   → Nf {suc n} Γ (subnType sub T) -- Tsubbed
--   → (args : Args Γ (subnType sub T) nOut TOut) -- Tsubbed)
--   → Nf Γ TOut
-- appNfSOtherSubs {n} (Π A B) sub e args with subst (λ T → Nf {suc n} _ T) (ΠsubnType≡ sub) e
-- ... | e' = {! e'  !}
-- appNfSOtherSubs (cumu T) sub e args = {!   !}
-- appNfSOtherSubs (type _) sub e args = {!   !}
-- appNfSOtherSubs (fromE x) sub e args = {!   !}

TODO TODO TODO:

{-
THREE things that could potentially not work that I need to figure out:
1) Does the error when unquoting idSubn defintion represent just a glitch, or
    also something real? Think about what its saying, also try to get it to
    compile by switching to the other form of mutual recursion in Agda.
2) Prove commutative property for lambda case of appNfS
3) subAllNf doesn't really fit into inductive structure of proof? Or does it?
    It definetely would if it was the other design of list of 1Subs.
-}
