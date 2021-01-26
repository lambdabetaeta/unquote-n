open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (suc ; Fin)

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

-- idea is to define append1sub as composition of liftTSub and subbo
subbo : ∀{Δ₁ Δ₂ n} → TSub (Δ₁ , n) (Δ₂ , n) → Type n Δ₂ → TSub (Δ₁ , n) Δ₂
subbo sub T x = subType (append1sub idSub T) (sub x)

_∘_ : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(sub₁ ∘ sub₂) x = subType sub₂ (sub₁ x)

-- _∼_ : ∀{l} → {A B : Set l} → (f g : A → B) → Set l
-- f ∼ g = ∀{x} → f x ≡ g x
_∼_ : ∀{Δ₁ Δ₂} → (sub₁ sub₂ : TSub Δ₁ Δ₂) → Set
sub₁ ∼ sub₂ = ∀{n x} → sub₁ {n} x ≡ sub₂ {n} x -- TODO: make x not implicit

liftFact : ∀{Δ₁ Δ₂ n} → (sub₁ sub₂ : TSub Δ₁ Δ₂)
  → sub₁ ∼ sub₂ → liftTSub {_} {_} {n} sub₁ ∼ liftTSub sub₂
liftFact sub₁ sub₂ p {_} {same} = refl
liftFact sub₁ sub₂ p {_} {next x} = cong (λ T → renType weaken1Δ T) p

lift∘comm : ∀{Δ₁ Δ₂ Δ₃ n} → (sub₁ : TSub Δ₁ Δ₂) → (sub₂ : TSub Δ₂ Δ₃)
  → liftTSub {_} {_} {n} (sub₁ ∘ sub₂) ∼ (liftTSub sub₁ ∘ liftTSub sub₂)
lift∘comm sub₁ sub₂ {n} {same} = refl
lift∘comm sub₁ sub₂ {n} {next x} = {! (lift∘comm sub₁ sub₂)  !}

funextsub : ∀{Δ₁ Δ₂ n} → (T : Type n Δ₁) → (sub₁ sub₂ : TSub Δ₁ Δ₂)
  → sub₁ ∼ sub₂
  → subType sub₁ T ≡ subType sub₂ T
funextsub (Var x) sub₁ sub₂ p = p
funextsub (A ⇒ B) sub₁ sub₂ p
  = cong₂ _⇒_ (funextsub A sub₁ sub₂ p) (funextsub B sub₁ sub₂ p)
funextsub (⋁ {n} T) sub₁ sub₂ p
  = cong ⋁ (funextsub T (liftTSub {_} {_} {n} sub₁) (liftTSub sub₂) λ {_} {x} → liftFact sub₁ sub₂ p {_} {x} )
funextsub (cumu T) sub₁ sub₂ p = cong cumu (funextsub T sub₁ sub₂ p)

subTypeShuffle : ∀{Δ₁ Δ₂ Δ₃ n} → (T : Type n Δ₁)
  → (sub₁ : TSub Δ₁ Δ₂) → (sub₂ : TSub Δ₂ Δ₃)
  → (sub₃ : TSub Δ₁ Δ₃)
  → (sub₁ ∘ sub₂) ∼ sub₃
  → subType sub₂ (subType sub₁ T) ≡ subType (sub₁ ∘ sub₂) T
subTypeShuffle (Var x) sub₁ sub₂ sub₃ p = {!   !}
subTypeShuffle (A ⇒ B) sub₁ sub₂ sub₃ p
  = cong₂ _⇒_ (subTypeShuffle A sub₁ sub₂ sub₃ p) (subTypeShuffle B sub₁ sub₂ sub₃ p)
subTypeShuffle (⋁ T) sub₁ sub₂ sub₃ p
  = let p1 = subTypeShuffle T (liftTSub sub₁) (liftTSub sub₂) (liftTSub sub₃) {!   !}
    in let p2 = {!   !}
    in cong ⋁ (trans p1 p2)
-- TODO: think about functorial properties of lift????
subTypeShuffle (cumu T) sub₁ sub₂ sub₃ p
  = cong cumu (subTypeShuffle T sub₁ sub₂ sub₃ p)


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
    → Exp (Δ , n) (renΓ weaken1Δ Γ) T → Type n Δ → Exp Δ Γ (⋁ T)
  TApp : ∀{Δ Γ n} → {T : Type (suc n) (Δ , n)}
    → Exp Δ Γ (⋁ T)
    → (X : Type n Δ)
    → Exp Δ Γ (subType (append1sub idSub X) T)

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

-- TSubn :
TSubn : ℕ → TCtx → TCtx → Set
TSubn (suc n) Δ₁ Δ₂ = InTCtx Δ₁ n → Type n Δ₂
TSubn zero Δ₁ Δ₂ = ⊤

append1subn : ∀{n Δ₁ Δ₂} → TSubn (suc n) Δ₁ Δ₂ → Type n Δ₂ → TSubn (suc n) (Δ₁ , n) Δ₂
append1subn sub T same = T
append1subn sub T (next x) = sub x

data ArgCount : ∀{n Δ} → Type n Δ → Set where
  none : ∀{n Δ T} → ArgCount {n} {Δ} T
  one : ∀{n Δ A B} → ArgCount B → ArgCount {n} {Δ} (A ⇒ B)
  One : ∀{n Δ T} → (X : Type n Δ)
    → ArgCount {_} {Δ , n} T → ArgCount (⋁ T)
  cumu : ∀{n Δ T}
    → ArgCount {n} {Δ} T → ArgCount {suc n} (cumu T)

-- subArgCount : ∀{Δ₁ Δ₂ n} → (sub : TSub Δ₁ Δ₂) → (T : Type n Δ₁)
  -- → ArgCount T → ArgCount (subType sub T)

mutual
  -- partially unquoted Exp
  --            ↓      ↓                  ↓
  PUExp : ∀{n Δ Δ'} → (T : Type n Δ') → (sub : TSub Δ' Δ)
    → ArgCount (subType sub T) → Ctx Δ → Set
  PUExp (Var x) sub count Γ = {!   !}
  PUExp (A ⇒ B) sub (one count) Γ = (GExpImpl Γ sub A) → PUExp B sub count Γ
  PUExp (⋁ T) sub (One X count) Γ = PUExp T (append1sub sub X) {! count  !} Γ
  PUExp (cumu T) sub (cumu count) Γ = PUExp (subType sub T) idSub {! count  !} Γ
  PUExp T sub none Γ = Exp _ Γ (subType sub T)
  -- PUExp {n} {Δ} {Δ'} sub (none {_} {_} {_} {T}) Γ = Exp Δ Γ (subType sub T) -- TODO: should be Nf
  -- PUExp {n} sub (one {_} {_} {_} {A} count) Γ
  --   = (GExpImpl {n} Γ sub A) → PUExp {n} sub count Γ
  -- PUExp {n} sub (One X count) Γ
  --   = PUExp {n} (append1sub sub X) count Γ
  -- PUExp {suc n} {Δ} {Δ'} sub (cumu count) Γ = PUExp idSub count Γ -- NOTE: this step is what allows GExp to not be recursive: we only apply subs when decreasing level.
  -- TODO: think about if the above design of only applying subs at cumu case could be used to do inductive normalization of System-F, similar to how I do inductive normalization of STLC.

  -- Exp that can be partially unquoted to any amount
  APUExp : ∀{n Δ Δ'} → Ctx Δ → TSub Δ' Δ → Type n Δ' → Set
  APUExp {n} Γ sub T = (count : ArgCount (subType sub T)) → PUExp {n} T sub count Γ

  -- Exp that can be in a weaker context AND partially unquoted
  GExpImpl : ∀{n Δ Δ'} → Ctx Δ → TSub Δ' Δ → Type n Δ' → Set
  GExpImpl {n} Γ sub T = ∀{Γ'} → Ren Γ Γ' → APUExp {n} Γ' sub T

  GExp : ∀{n Δ} → Ctx Δ → Type n Δ → Set
  GExp Γ T = GExpImpl Γ idSub T

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub {Δ} Γ₁ Γ₂ = ∀{n T} → InCtx {n} Γ₁ T → GExp Γ₂ T

-- nApp : ∀{n Δ Δ' Γ T} → (sub : TSub Δ Δ')
--   → (count : ArgCount {n} T sub) → Exp Δ Γ T → PUExp sub count Γ
-- nApp sub none e = {! TsubExp sub e  !}
-- nApp sub (one count) e = {!   !} -- λ x → nApp count (app e (x idRen none))
-- -- nApp (One X count) e = nApp count (TApp {! e  !} {! X  !} ) -- TODO: subExp?
-- nApp sub (One X count) e = {!   !} -- nApp count {! TApp e X  !} -- TODO: subExp?
-- nApp sub (cumu count) e = {! e  !} -- TODO: need cumu in Exp, maybe need Nf and Ne.

-- idSub : ∀{Δ Γ} → Sub {Δ} Γ Γ
-- idSub x ren count = nApp count (var (ren x))

{-
TODO: THE PLAN!

I'm going to see if its possible for subs to only appear in GExp, aka minimal subs

-- TODO: think about functorial properties of lift????

Basically, theres a bunch of annoying stuff with showing that different subs are actually
the same as each other. What I'm currently doing is in TLambda case of PUExp, there is
I'm going to rewrite append1sub as subbo ∘ liftSub, then use subTypeShuffle
and subCount to be able to convert count to the correct type.

CURRENT THOUGHTS:
Probably its possible to make all this work in the end. But,
I feel that there should be a way to normalize System F without proving a
whole bunch of shit. In particular, any design which uses ≡ PropositionalEquality
I think is probably wrong.

Maybe there is a better represenation of Sub which makes things better?
Like Sub = (f : InTCtx Δ → Type Δ) with proof that (f (A ⇒ B) ≡ f A ⇒ f B) etc?

Or have all parametrized by Typos?  <=== try this first I think. TODO

-}
