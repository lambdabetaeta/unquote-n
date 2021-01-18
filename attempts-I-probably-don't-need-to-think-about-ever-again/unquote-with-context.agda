open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Sum

data Type : Set where
  _⇒_ : Type → Type → Type
  bool : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

-- TODO: TODO TODO: Replace InCtx with InCtx2 in subsequent code
data InCtx2 : Ctx → Type → Set where
  same : ∀{Γ T} → InCtx2 (Γ , T) T
  next : ∀{Γ T A} → InCtx2 Γ A → InCtx2 (Γ , T) A

data InCtx : (Γ : Ctx) → Set where
  same : ∀{Γ T} → InCtx (Γ , T)
  next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)

Tat : ∀{Γ} → InCtx Γ → Type
Tat (same {Γ} {T}) = T
Tat (next icx) = Tat icx

Γat : ∀{Γ} → InCtx Γ → Ctx
Γat (same {Γ} {T}) = Γ
Γat (next icx) = Γat icx

data Exp : Ctx → Type → Set where
  var : ∀{Γ} → (icx : InCtx Γ) → Exp Γ (Tat icx)
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  true : ∀{Γ} → Exp Γ bool
  false : ∀{Γ} → Exp Γ bool
  if : ∀{Γ A} → Exp Γ bool → Exp Γ A → Exp Γ A → Exp Γ A

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = (x : InCtx Γ₁) → Σ (InCtx Γ₂) (λ x' → Tat x' ≡ Tat x)

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren ren = (next ren) , refl

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

liftRen : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
liftRen ren same = same , refl
liftRen ren (next itc) = let (itc' , p) = ren itc
  in next itc' , p

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x , refl

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → let (y , p) = s₁ x
  in let (z , q) = s₂ y
  in z , trans q p

weaken : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Exp Γ₁ T → Exp Γ₂ T
weaken {Γ₁} {Γ₂} ren (var icx) = let (icx' , p) = ren icx in
  subst (λ T → Exp Γ₂ T) p (var icx')
weaken ren (lambda e) = lambda (weaken (liftRen ren) e)
weaken ren (app e₁ e₂) = app (weaken ren e₁) (weaken ren e₂)
weaken ren true = true
weaken ren false = false
weaken ren (if e e₁ e₂) = if (weaken ren e) (weaken ren e₁) (weaken ren e₂)

data ArgCount : Type → Set where
  none : ∀{T} → ArgCount T
  one : ∀{A B} → ArgCount B → ArgCount (A ⇒ B)

{-
  This file is not an implementation of unquote-n.

  Instead, it will unquote into context. E.g.
  Convert first n arguments to context, so e.g. if
  e : Exp ∅ (A → B → C → D)
  unquote 2 e : Exp (A , B) (C -> D)
-}

addToCtx : ∀{T} → ArgCount T → Ctx → Ctx
addToCtx none Γ = Γ
addToCtx (one {A} count) Γ = addToCtx count (Γ , A)

output : ∀{T} → ArgCount T → Type
output (none {T}) = T
output (one count) = output count

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = (x : InCtx Γ₁) → Exp Γ₂ (Tat x)

liftSub : ∀{Γ Γ' A} → Sub Γ Γ' → Sub (Γ , A) (Γ' , A)
liftSub sub same = var same
liftSub sub (next x) = weaken weaken1Ren (sub x)

append1sub : ∀{Γ Γ' A} → Sub Γ Γ' → Exp Γ' A → Sub (Γ , A) Γ'
append1sub sub e same = e
append1sub sub e (next x) = sub x

weakenSub : ∀{Γ Γ' T} → (count : ArgCount T)
  → Sub (addToCtx count Γ) Γ' → Sub Γ Γ'
weakenSub none sub = sub
weakenSub (one count) sub x = (weakenSub count sub) (next x)

idSub : ∀{Γ} → Sub Γ Γ
idSub x = var x
weaken1Sub : ∀{Γ A} → Sub Γ (Γ , A)
weaken1Sub x = var (next x)

_o_ : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₂ Γ₃ → Ren Γ₁ Γ₂ → Sub Γ₁ Γ₃
_o_ s r x = let (y , p) = r x in subst (λ T → Exp _ T) p (s y)

helper : ∀{Γ' Γ₁ Γ₂ A} → ((x : InCtx Γ₂) → Σ (InCtx Γ₁) (λ y → Tat y ≡ Tat x) ⊎ Exp Γ' (Tat x))
  → ((x : InCtx (Γ₂ , A)) → Σ (InCtx (Γ₁ , A)) (λ y → Tat y ≡ Tat x) ⊎ Exp Γ' (Tat x))
helper split same = inj₁ (same , refl)
helper split (next x) with split x
... | inj₁ (y , p) = inj₁ (next y , p)
... | inj₂ e = inj₂ e


somethingSomethingCombineThings : ∀{Γ₁ Γ₂ Γ' T} → (count : ArgCount T)
  → ((x : InCtx Γ₂) → ((Σ (InCtx Γ₁) (λ y → Tat y ≡ Tat x)) ⊎ Exp Γ' (Tat x)))
  → Sub (addToCtx count Γ₁) Γ'
  → Sub (addToCtx count Γ₂) Γ'
somethingSomethingCombineThings none split sub x with split x
... | inj₁ (y , p) = subst (λ T → Exp _ T) p (sub y)
... | inj₂ e = e
somethingSomethingCombineThings {Γ₁} {Γ₂} (one {A} count) split sub
  = somethingSomethingCombineThings {Γ₁ , A} {Γ₂ , A} count (helper split) sub

helper2 : ∀{Γ A Γ'}
  → Exp Γ' A
  → ((x : InCtx (Γ , A)) → Σ (InCtx Γ) (λ y → Tat y ≡ Tat x) ⊎ Exp Γ' (Tat x))
helper2 e same = inj₂ e
helper2 e (next x) = inj₁ (x , refl)
append1AfterCount : ∀{Γ Γ' A T} → (count : ArgCount T)
  → Sub (addToCtx count Γ) Γ'
  → Exp Γ' A → Sub (addToCtx count (Γ , A)) Γ'
append1AfterCount count sub e = somethingSomethingCombineThings count (helper2 e) sub

subForgetCount : ∀{Γ Γ' T} → (count : ArgCount T)
  → Sub (addToCtx count Γ) Γ' → Sub Γ Γ'
subForgetCount none sub = sub
subForgetCount (one count) sub x = subForgetCount count sub (next x)

nApp : ∀{Γ Γ' T} → (count : ArgCount T) → Sub (addToCtx count Γ) Γ'
  → Exp Γ' T -- sub icx
  → Exp Γ' (output count)
nApp none sub e = e
nApp (one count) sub e = nApp count sub (app e (subForgetCount count sub same))

data Three : Set where
  t f o : Three

check : ∀{Γ T} → Exp Γ T → Three
check true = t
check false = f
check _ = o

unq : ∀{Γ Γ' T} → Exp Γ T → (count : ArgCount T)
  → Sub (addToCtx count Γ) Γ' -- For each var in (addToCtx count Γ), either provide a value, or simply output a var in Γ'.
  → Exp Γ' (output count)
unq (var icx) count sub = nApp count sub ((weakenSub count sub) icx) -- nApp
unq (lambda e) none sub = lambda (unq e none (liftSub sub))
unq (lambda e) (one count) sub = unq e count sub
unq (app {Γ} {A} {B} e₁ e₂) count sub
  = let n₂ = unq e₂ none (weakenSub count sub)
    in unq e₁ (one count) (append1AfterCount count sub n₂)
unq true none sub = true
unq false none sub = false
unq (if e e₁ e₂) count sub with check (unq e none (subForgetCount count sub))
... | t = unq e₁ count sub
... | f = unq e₂ count sub
... | o = if (unq e none (subForgetCount count sub))
  (unq e₁ count sub)
  (unq e₂ count sub)

normalize : ∀{Γ T} → Exp Γ T → Exp Γ T
normalize e = unq e none idSub


-- This code badly needs some rewriting, but I'll test it first:

code : Exp ∅ bool
code = app (lambda (var same)) true

res : normalize code ≡ true
res = refl

code2 : Exp ∅ (bool ⇒ bool)
code2 = lambda (app (lambda (var same)) true)

res2 : normalize code2 ≡ (lambda true)
res2 = refl

code3 : Exp ∅ (bool ⇒ bool)
code3 = app (lambda (lambda (var same))) true

res3 : normalize code3 ≡ (lambda (var same))
res3 = refl

code4 : Exp ∅ (bool ⇒ (bool ⇒ bool))
code4 = lambda (lambda (var same))

res4 : normalize code4 ≡ code4
res4 = refl

code5 : Exp ∅ (bool ⇒ bool)
code5 = app (lambda (lambda (var (next same)))) true

res5 : normalize code5 ≡ (lambda true)
res5 = refl
