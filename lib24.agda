{- 
Library for COMP4074.PPT

upto lecture 11
-}

{- products and sums -}

infix 10 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

variable
  A B C : Set

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b) -- C-c C-,
uncurry : (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

infix 5 _⊎_
data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase f = (λ a → f (inj₁ a)) , λ b → f (inj₂ b)

--case' : (A → C) × (B → C) → (A ⊎ B → C)
--case' = uncurry case

record ⊤ : Set where
  constructor tt

open ⊤ public

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : Bool → A → A → A
if true then x else y = x
if false then x else y = y

{- bool logic -}

_&_ : Bool → Bool → Bool
true & y = y
false & y = false

{- ∣ = \mid -}

_∣_ : Bool → Bool → Bool
true ∣ y = true
false ∣ y = y

!_ : Bool → Bool
! true = false
! false = true

_⇒b_ : Bool → Bool → Bool
true ⇒b y = y
false ⇒b y = true

{- prop logic -}

prop = Set

variable
  P Q R : prop

infix 3 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q

infixr 1 _⇒_
_⇒_ : prop → prop → prop
P ⇒ Q = P → Q

False : prop
False = ⊥

True : prop
True = ⊤

¬_ : prop → prop
¬ P = P ⇒ False

infix 0 _⇔_
_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

efq : False ⇒ P
efq = case⊥

{- classical principles -}

TND : prop → prop
TND P = P ∨ ¬ P

RAA : prop → prop
RAA P = ¬ ¬ P ⇒ P

tnd⇒raa : TND P ⇒ RAA P
tnd⇒raa (inj₁ p) nnp = p
tnd⇒raa (inj₂ np) nnp = efq (nnp np)

nnpnp : ¬ ¬ (P ∨ ¬ P)
nnpnp h = h (inj₂ (λ p → h (inj₁ p)))

raa⇒tnd : RAA (P ∨ ¬ P) ⇒ TND P
raa⇒tnd raa = raa nnpnp

{- natural numbers -}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infix 6 _+_ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infix 7 _*_ 

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

infix 8 _^_ 

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * m ^ n

{- Lists -}

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A -- \::

map : (A → B) → List A → List B
map f [] = []
map f (a ∷ as) = f a ∷ map f as

_++_ :  List A → List A → List A
[] ++ l2 = l2
(x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)
{- Streams -}

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    head : A
    tail : Stream A

open Stream

mapS : (A → B) → Stream A → Stream B
head (mapS f as) = f (head as)
tail (mapS f as) = mapS f (tail as)

{- conatural numbers -}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞

open ℕ∞

zero∞ : ℕ∞
pred∞ zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
... | nothing = pred∞ n
... | just m' = just (m' +∞ n)

variable W : Set

CoItℕ∞ : (W → Maybe W) → W → ℕ∞
pred∞ (CoItℕ∞ p x) with p x
... | nothing = nothing
... | just x' = just (CoItℕ∞ p x')

{- Vectors and Fin -}

variable i j k m n : ℕ

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_++v_ : Vec A m → Vec A n → Vec A (m + n)
[] ++v ys = ys
(x ∷ xs) ++v ys = x ∷ (xs ++v ys)

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

_!!v_ : Vec A n → Fin n → A
(x ∷ xs) !!v zero = x
(x ∷ xs) !!v suc i = xs !!v i

{- Σ-types -}

record Σ(A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

syntax Σ A (λ x → P)  = Σ[ x ∈ A ] P
-- (x : A) × B 

{- Π - types -}

Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x

syntax Π A (λ x → P)  = Π[ x ∈ A ] P

{- isomorphism without the proofs -}

infix 0 _~_

record _~_ (X Y : Set) : Set where
  field
    φ : X → Y -- \phi
    ψ : Y → X -- \psi
    -- ψ ∘ φ = id
    -- φ ∘ ψ = id

{- predicate logic -}

All : (A : Set)(P : A → prop) → prop
All A P = (x : A) → P x
Ex : (A : Set)(P : A → prop) → prop
Ex A P = Σ[ x ∈  A ] P x
syntax All A (λ x → P)  = ∀[ x ∈ A ] P  
infix 0 All
syntax Ex A (λ x → P) = ∃[ x ∈ A ] P
infix 0 Ex

variable PP QQ : A → prop

{- Equality -}

data _≡_ : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans h refl = h

cong : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

{-
  uncong : (f : A → B) → {a b : A} → f a ≡ f b → a ≡ b
  uncong f refl = refl
-}

subst : (P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst P refl p = p

sym-s : {a b : A} → a ≡ b → b ≡ a
sym-s {A} {a} {b} p = subst (λ x → x ≡ a) p refl

trans-s : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans-s {a = a} p q = subst (λ x → a ≡ x) q p

cong-s : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong-s f {a = a} p = subst (λ x → f a ≡ f x) p refl

module ≡-Reasoning {A : Set} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡˘⟨_⟩_ : ∀ (x {y z} : A) → y ≡ x → y ≡ z → x ≡ z
  _ ≡˘⟨ y≡x ⟩ y≡z = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

open  ≡-Reasoning public

{- ℕ with addition is a commutative monoid -}

lneutr+ : {n : ℕ} → 0 + n ≡ n
lneutr+ {n} = refl

rneutr+ : {n : ℕ} → n + 0 ≡ n
rneutr+ {zero} = refl
rneutr+ {suc n} = cong suc (rneutr+ {n})
-- suc n + 0 ≡ suc n
-- suc n + 0 = suc (n + 0)
-- C-c C-, : show normalized goal
-- C-u C-c C-, non-normalized goal
-- induction becomes recursion (and pattern matching)

assoc+ : {l m n : ℕ} → (l + m) + n ≡ l + (m + n)
assoc+ {zero} {m} {n} = refl
assoc+ {suc l} {m} {n} = cong suc (assoc+ {l} {m} {n})
-- (suc l + m) + n = (suc (l + m) + n) = suc ((l + m) + n)
-- (suc l) + (m + n) = suc (l + (m + n))

comm-suc : {l m : ℕ} → suc (m + l) ≡ m + suc l
comm-suc {l} {zero} = refl
comm-suc {l} {suc m} = cong suc comm-suc

comm+ : {l m : ℕ} → l + m ≡ m + l
comm+ {zero} {m} = sym (rneutr+ {m})
comm+ {suc l} {m} = 
  suc (l + m)
    ≡⟨ cong suc (comm+ {l} {m}) ⟩
  suc (m + l)
    ≡⟨ comm-suc ⟩
  m + suc l
    ∎

{- Decidable -}

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : ¬ P → Dec P

{- Faking strings -}

postulate String : Set
{-# BUILTIN STRING String #-}

{- Natural deduction -}

data Form : Set where
  Var : String → Form
  _[⇒]_ : Form → Form → Form

infixr 10 _[⇒]_

Con : Set
Con = List Form

-- de Brujn : nameless dummies

data _⊢_ : Con → Form → Set where
  zero : {Γ : Con}{P : Form} → (P ∷ Γ) ⊢ P
  suc : {Γ : Con}{P Q : Form}
         → Γ ⊢ P → (Q ∷ Γ) ⊢ P
  lam : {Γ : Con}{P Q : Form}
      → (P ∷ Γ) ⊢ Q → Γ ⊢ (P [⇒] Q)  
  app : {Γ : Con}{P Q : Form}
      → Γ ⊢ (P [⇒] Q) → Γ ⊢ P → Γ ⊢ Q
