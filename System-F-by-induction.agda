open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)
open import Data.Sum

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

-- TODO: call TSub, call the subv ESub. (expression and type)
subNf : ∀{n Δ₁ Δ₂ Γ T} → (sub : TSub Δ₁ Δ₂)
  → Nf {n} Δ₁ Γ T
  → Nf {n} Δ₂ (subΓ sub Γ) (subType sub T)
subNf sub (lambda e) = lambda (subNf sub e)
subNf {n} {Δ₁} {Δ₂} {Γ} {T} sub (Tlambda e)
  = Tlambda {! subNf {n} {Δ₁ , n} {Δ₂ , n} ? ?  !}
subNf sub (ne (varapp count icx x)) = {!   !}
subNf sub (cumu e) = {!   !}

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

-- idSubFact1 : ∀{Δ n} → idSub {Δ , n} ∼ (liftTSub idSub)
-- idSubFact1 = {!   !}

-- idSubFact : ∀{n Δ₁ Δ₂} → (T : Type n Δ₁) → T ≡ subType idSub T
-- idSubFact (Var x) = refl
-- idSubFact (A ⇒ B) = cong₂ (_⇒_) (idSubFact A) (idSubFact B)
-- idSubFact (⋁ T) = {! cong ⋁ (idSubFact T)  !}
-- idSubFact (cumu T) = cong cumu (idSubFact T)

{-
mutual
  --             ↓
  subv : ∀{n m Δ Δ' Γ Te Tsub Tsub'} → {sub : TSub Δ' Δ}
    → Tsub' ≡ subType sub Tsub
    → (icx : InCtx {n} {Δ} Γ Tsub')
    → (toSub : Nf Δ (subCtx icx) Tsub')
    → Nf {m} Δ Γ Te → Nf Δ (subCtx icx) Te
  subv = {!   !}
  --           ↓           ↓                ↓   makes a Typo
  appv : ∀{n Δ Δ' Γ T'} → (T : Type n Δ') → (sub : TSub Δ' Δ)
    → T' ≡ subType sub T
    → (e : Nf {n} Δ Γ T')
    → (count : ArgCount T')
    → inputs count Γ
    → Nf Δ Γ (output count)
  appv T sub p (lambda e) none tt = lambda e
  appv (A ⇒ B) sub p (lambda e) (one count) (a , inputs)
    -- = appv B idSub (idSubFact B) (subv (idSubFact A) same a e) count inputs
    = appv B {!   !} {!   !} {!   !} count inputs
  appv (⋁ T) sub p (Tlambda e) none tt = Tlambda e
  appv (⋁ T) sub p (Tlambda e) (One X count) inputs
    = {!   !}
    -- = appv (append1sub sub X) {!   !} {! e  !} {! count  !} inputs
  appv T sub p (ne x) count inputs = {!   !}

  -- can't split on e, because not proper induction.
  -- NOTE : this proves that we can't use this design, need Nf and Ne
  -- to be parametrized by Typo, not just Type.
-}

mutual
  --             ↓
  -- subv1 : ∀{n m Δ Δ' Γ Te Tsub Tsub'} → {sub : TSub Δ' Δ}
  --   → Tsub' ≡ subType sub Tsub
  --   → (icx : InCtx {n} {Δ} Γ Tsub')
  --   → (toSub : Nf Δ (subCtx icx) Tsub')
  --   → Nf {m} Δ Γ Te → Nf Δ (subCtx icx) Te
  -- subv1 = {!   !}
  --           ↓           ↓                ↓   makes a Typo
  appv1 : ∀{n Δ Δ' Γ} → (T : Type n Δ') → (sub : TSub Δ' Δ)
    → (e : Nf {n} Δ' Γ T)
    → (count : ArgCount T) -- TODO: wrong, wont allow full application of e.g. ∀X . X → X
    → inputs count Γ
    → Nf Δ (subΓ sub Γ) (subType sub (output count))
  appv1 (A ⇒ B) sub (lambda e) none tt = subNf sub (lambda e)
  appv1 (A ⇒ B) sub (lambda e) (one count) (a , inputs)
    = appv1 B sub {! subv1 sub a e  !} count inputs
  appv1 (⋁ T) sub (Tlambda e) none tt = subNf sub (Tlambda e)
  appv1 (⋁ T) sub (Tlambda e) (One X count) inputs
    = let a = appv1 T (append1sub sub (subType sub X))
              e count inputs
      in {! a  !} -- Same as lambda case, need to do sub and app. Just that its a type sub!
  appv1 T sub (ne x) count inputs = {!   !}
  appv1 (cumu T) sub (cumu e) none inputs = subNf sub (cumu e)
  appv1 (cumu T) sub (cumu e) (cumu count) inputs
    = appv1 T sub e count inputs -- TODO this is wrong, should be applying sub.


{-
TODO

Where I'm at in this file is rethinking how the proof works on paper and trying
to make it happen here.

-- Implement subNf, which should be called TsubNf

-}
