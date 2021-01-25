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

{-
This idea behind this file is that the induction proof for STLC is trivial on paper,
and can be easily extended to (predicative) System-F on paper by using a lexographical
ordering on type levels present in a type. But this is cumbersome in a theorem
prover, and its unclear if it can be used in an intrinsically-typed way.
Therefore, I have come up with a representation of System-F types, namely
"Typo" below, on which the output type of ∀X . T (which is T[X ↦ A] for some A)
can be represented in a way that is a STRUCTURAL SUBEXPRESSION of T.
Thus the proof can be done with simple induction principles.
-}

Typo : ℕ → TCtx → Set -- TODO: change name
Typo n Δ = Σ TCtx (λ Δ' → TSub Δ' Δ × Type n Δ')
-- So, the idea is that some Typos are equivalent
-- (∅ , idSub , T) = ([n] , [X ↦ T] , X)
-- ESSENTIALLY, (Δ' , sub , T) represents the type sub(T)
-- but if f : (Δ' , sub ,∀X.T), then f A : ([Δ' , n] , [sub , X ↦ A] , T)
-- so the T is structurally smaller!
-- But why doesn't this cause a problem when we get to the variable case?
-- because in the cumu case, all subs are applied. And you must go down a level before
-- getting to X anyway, as it is at one level lower.

data ArgCount2 : ∀{n Δ} → Typo n Δ → Set where
  none : ∀{n Δ} → {T : Typo n Δ} → ArgCount2 T
  one : ∀{n Δ Δ' A B} → {sub : TSub Δ' Δ} → ArgCount2 {n} (Δ' , sub , B)
    → ArgCount2 (Δ' , sub , A ⇒ B)
  One : ∀{n Δ Δ' T} → {sub : TSub Δ' Δ} → (X : Type n Δ)
    → ArgCount2 ((Δ' , n) , (append1sub sub X) , T)
    → ArgCount2 (Δ' , sub , ⋁ T)
  cumu : ∀{n Δ Δ' T} → {sub : TSub Δ' Δ}
    → ArgCount2 {n} (Δ , idSub , subType sub T)
    → ArgCount2 (Δ' , sub , cumu T)

outputN : ∀{n Δ} → (T : Typo n Δ) → ArgCount2 T → ℕ
outputN {n} T none = n
outputN (Δ' , sub , A ⇒ B) (one count) = outputN _ count
outputN (Δ' , sub , (⋁ T)) (One X count) = outputN _ count
outputN (Δ' , sub , (cumu T)) (cumu count) = outputN _ count

output : ∀{n Δ} → (T : Typo n Δ) → (count : ArgCount2 T)
  → Typo (outputN T count) Δ
output T none = T
output (Δ' , sub , A ⇒ B) (one count) = output (Δ' , sub , B) count
output {suc n} (Δ' , sub , ⋁ T) (One X count)
  = output ((Δ' , n) , append1sub sub X , T) count -- TODO: is this line right?
output {_} {Δ} (Δ' , sub , cumu T) (cumu count)
  = output (Δ , idSub , subType sub T) count
  -- TODO TODO TODO TODO TODO: the above makes no sense. Definitely need
  -- to have outputN, which determines the outputN, rather than using cumu constructor
  -- in output.

  --            ↓       ↓                  ↓   make Typo
outputΓ : ∀{n Δ Δ'} → {sub : TSub Δ' Δ} → (T : Type n Δ')
  → (count : ArgCount2 (Δ' , sub , T))
  → Ctx Δ' → Ctx (proj₁ (output _ count))
outputΓ T none Γ = Γ
outputΓ (A ⇒ B) (one count) Γ = outputΓ B count Γ
outputΓ (⋁ T) (One X count) Γ = outputΓ T count (renΓ weaken1Δ Γ)
outputΓ {_} {_} {_} {sub} (cumu T) (cumu count) Γ
  = outputΓ (subType sub T) count (subΓ sub Γ)

-- TODO: need all Contexts to be in Δ instead of Δ'
mutual
  --           THIS↓  THIS↓                    and THIS↓     make a Typo
  data Nf : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → Ctx Δ' → Type n Δ' → Set where
    lambda : ∀{n Δ Δ' Γ A B} → {sub : TSub Δ' Δ}
      → Nf {n} sub (Γ , A) B → Nf sub Γ (A ⇒ B)
    Tlambda : ∀{Δ Δ' n Γ T} → {sub : TSub Δ' Δ} -- TODO: I got Tlambda case to typecheck, but is it correct?
      → Nf {suc n} {Δ , n} {Δ' , n} (liftTSub sub) (renΓ weaken1Δ Γ) T
      → Nf {suc n} {Δ} {Δ'} sub Γ (⋁ T)
    cumu : ∀{Δ Δ' n T Γ} → {sub : TSub Δ' Δ}
      → Nf {n} {Δ} {Δ} idSub (subΓ sub Γ) (subType sub T)
      → Nf {suc n} {Δ} {Δ'} sub Γ (cumu T)
    ne : ∀{n Δ Δ' Γ T} → {sub : TSub Δ Δ'} → Ne {n} sub Γ T → Nf {n} sub Γ T

  data Ne : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → Ctx Δ' → Type n Δ' → Set where
    --             ↓         ↓                  ↓ makes a Typo
    varapp : ∀{n Δ Δ' Γ} → (sub : TSub Δ' Δ) → (T : Type n Δ')
      → (count : ArgCount2 (Δ' , sub , T))
      → (icx : InCtx Γ T)
      → inputs sub _ count Γ
      → let (Δ'out , subout , Tout) = output (Δ' , sub , T) count
        in Ne subout (outputΓ _ count Γ) Tout

  -- TODO: maybe merge inputs and ArgCount, currently ArgCount holds TApp args, while inputs holds app args. Maybe ArgCount should just hold all args?
  inputs : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → (T : Type n Δ')
    → ArgCount2 (Δ' , sub , T) → Ctx Δ' → Set
  inputs sub T none Γ = ⊤
  inputs sub (A ⇒ B) (one count) Γ = Nf sub Γ A × inputs sub B count Γ
  inputs sub (⋁ T) (One X count) Γ = inputs (append1sub sub X) T count (renΓ weaken1Δ Γ) -- TODO: again, is this correct?
  inputs sub (cumu T) (cumu count) Γ = inputs idSub (subType sub T) count (subΓ sub Γ)

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

subTrans : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
subTrans sub₁ sub₂ x = subType sub₂ (sub₁ x)

--                ↓    ↓      ↓  make the Typo
subNf : ∀{n Δ₁ Δ₂ Δ' Γ T} → {subT : TSub Δ' Δ₁} → (sub : TSub Δ₁ Δ₂)
  → Nf {n} {Δ₁} {Δ'} subT Γ T
  → Nf {n} {Δ₂} {Δ'} (subTrans subT sub) Γ T
subNf sub (lambda e) = lambda (subNf sub e)
subNf sub (Tlambda e) = Tlambda {! subNf ? e  !}
subNf sub (cumu e) = cumu {! subNf sub e  !}
subNf sub (ne x) = {!   !}

  -- data Nf : ∀{n Δ Δ'} → (sub : TSub Δ' Δ) → Ctx Δ' → Type n Δ' → Set where
mutual
  -- subv : ∀{n m Δ Δ' Δ'e Γ T T'} → {sub : TSub Δ' Δ} → {sube : TSub Δ'e Δ}
  --   → (icx : InCtx {n} {Δ'} Γ T)
  --   → (toSub : Nf sub (subCtx icx) T)
  -- --   -- TODO: only toSub is part of induction here. e arg should have
  -- --   -- its own sub. Basically e is just parametrized by ANY sub.
  --   → Nf {m} sube Γ T' → Nf sube (subCtx icx) T'
  -- subv x toSub e = {!   !}

  appv : ∀{n Δ Δ' Γ T} → {sub : TSub Δ' Δ} → (e : Nf {n} sub Γ T)
    → (count : ArgCount2 (Δ' , sub , T))
    → inputs sub T count Γ
    → let (Δ'out , subout , Tout) = output _ count
      in  Nf subout (outputΓ _ count Γ) Tout
  appv (lambda e) none tt = lambda e
  appv (lambda e) (one count) (a , inputs)
    -- = appv (subv same a e) count inputs
    = appv {! subv same a ?  !} count inputs
  appv (Tlambda e) none tt = Tlambda e
  appv {_} {_} {_} {_} {_} {sub} (Tlambda e) (One X count) inputs
    -- = let a = subNf (append1sub sub X) {! e  !} in {!   !}
    = let a = subNf (append1sub {!   !} X) e in {!   !}
    -- = appv {! subNf (append1sub sub X) e  !} count inputs
  appv (cumu e) none tt = cumu e
  appv (cumu e) (cumu count) inputs
    = appv {_} {_} {_} {_} {_} {idSub} e count inputs -- idSub arg unecessary, just to show how it works!
  appv (ne (varapp sub T count₁ icx inputs₁)) count inputs₂
    = {!   !}


{-

-- NOTE: I see no reason that there should be done with Pre instead of Ren

weakenΓ : ∀{Δ n Γ} → Pre {Δ} Γ → Type n Δ → Ctx Δ
weakenΓ (same {_} {Γ}) A = Γ , A
weakenΓ (next {_} {Γ} {_} {T} pre) A = (weakenΓ pre A) , T

weakenICX : ∀{Δ n m Γ T} → (pre : Pre {Δ} Γ) → (W : Type n Δ)
  → (icx : InCtx {m} Γ T) → InCtx (weakenΓ pre W) T
weakenICX same W x = next x
weakenICX (next pre) W same = same
weakenICX (next pre) W (next x) = next (weakenICX pre W x)

weakenNf : ∀{n m Δ Γ T} → (pre : Pre Γ) → (W : Type n Δ)
  → Nf Δ Γ T → Nf {m} Δ (weakenΓ pre W) T

weakenInputs : ∀{n m Δ Δ' Γ T} → {sub : TSub Δ Δ'} → (pre : Pre Γ)
  → (W : Type n Δ')
  → (count : ArgCount {m} T sub)
  → inputs sub count Γ
  → inputs sub count (weakenΓ pre W)
weakenInputs pre W none inputs = tt
weakenInputs pre W (one count) (e , inputs)
  = weakenNf pre W e , weakenInputs pre W count inputs
weakenInputs pre W (One X count) inputs = weakenInputs pre W count inputs
weakenInputs pre W (cumu count) inputs = weakenInputs pre W count inputs

weakenNe : ∀{n m Δ Γ T} → (pre : Pre Γ) → (W : Type n Δ)
  → Ne Δ Γ T → Ne {m} Δ (weakenΓ pre W) T
weakenNe pre W (TApp e X) = TApp (weakenNe pre W e) X
weakenNe pre W (varapp count x inputs)
  = varapp count (weakenICX pre W x) (weakenInputs pre W count inputs)
weakenNf pre W (ne e) = ne (weakenNe pre W e)
weakenNf pre W (lambda v) = lambda (weakenNf (next pre) W v)
weakenNf pre W (Tlambda e) = Tlambda {! weakenNf ? ? e !}

weakenNf' : ∀{n m Δ Δ' Γ T} → {sub : TSub Δ Δ'} → (pre : Pre Γ)
  → (W : Type n Δ')
  → Nf Δ Γ T → Nf {m} Δ' {! weakenΓ pre ?  !}{-weakenΓ pre W-} (subType sub T)
weakenNf' = {!   !}
-}

{-
TODO list to fix things.
Maybe when I fix all of these things, the file will work.
Hopefully, I'll at least understand why it doesn't work.

1) Understand whats wrong in TLambda case of App.
  1 a) consider adding the X argument into TLambda case of Nf
      so that it uses append1sub isntead of liftTSub
  1 b) TODO Maybe need subNf, which subs types in an Nf.
    It would change Δ but keep Δ' the same. Because the Δ' is really just
    part of the Typo.
2) Make all Ctx in Δ instead of Δ'. Otherwise, can't define sub in way that
  makes sense, because need Γ for both e and toSub?
3) Think more carefully about proof on paper. See how this applies to things
  that I have here in this file.

Overall, the goal is to determine if this method really works or not by next
Wednesday.

TODO: is there any particular reason why ArgCount must be parametrized by
Typo instead of just Type?

-}
