module base where


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
  
variable A : Set

prop = Set

infix 10 _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

infix 5 _⊎_

data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infix 3 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q


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



All : (A : Set)(P : A → prop) → prop
All A P = (x : A) → P x

Ex : (A : Set)(P : A → prop) → prop
Ex A P = Σ[ x ∈  A ] P x

syntax All A (λ x → P)  = ∀[ x ∈ A ] P  
infix 0 All

syntax Ex A (λ x → P) = ∃[ x ∈ A ] P
infix 0 Ex

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

False : Set
False = ⊥

¬_ : Set → Set
¬ P = P → False



data Dec (P : Set) : Set where
  yes : P → Dec P
  no : ¬ P → Dec P

