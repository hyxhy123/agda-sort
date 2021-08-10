module Permutation where

open import base
open import List

variable a b : A
variable as bs cs as' bs' cs' : List A



data Add {A : Set} : A → List A → List A → Set where
  zero : Add a as (a ∷ as) 
  suc : Add a as bs → Add a (b ∷ as) (b ∷ bs)


data Perm {A : Set}  : List A → List A → Set where
  nil : Perm  [] []
  cons : Perm as cs → Add a cs bs → Perm (a ∷ as) bs
  
reflPerm : Perm as as
reflPerm {a} {[]} = nil
reflPerm {a} {x ∷ xs} = cons ( reflPerm {a} {xs} ) zero

lemma-add : Add a bs cs → Perm bs as → Perm cs (a ∷ as)
lemma-add zero  p = cons p zero
lemma-add (suc x) (cons p add) = cons (lemma-add x p) (suc add)

symPerm : Perm as bs → Perm bs as
symPerm nil = nil
symPerm (cons permab add) = lemma-add add (symPerm permab)

lemma-assoc : Add a as bs → Add b bs cs → Ex (List A) (λ bs' → (Add b as bs') × (Add a bs' cs))
lemma-assoc x zero = _ , (zero , (suc x))
lemma-assoc zero (suc y) = _ , (y , zero)
lemma-assoc (suc x) (suc y) with lemma-assoc x y
... | _ , (x' , y') = _ , (suc x' , suc y')

--need the third list bs'
Perm→Add×Perm  :  Add a bs cs  →  Perm cs cs'  → (Ex  (List A) (λ bs' → Add a bs' cs' × Perm bs bs') )
Perm→Add×Perm  zero (cons x₁ x)  = (_ , (x  , x₁))
Perm→Add×Perm  (suc x) (cons x₁ x₂) with Perm→Add×Perm  x x₁
... | ys , (z , zs ) with lemma-assoc z x₂
... | ys' , ( z' , zs' ) = ys' , (zs' , (cons zs z'))

transPerm : Perm as bs → Perm bs cs → Perm as cs
transPerm nil nil = nil
transPerm (cons x x₁) y with Perm→Add×Perm  x₁ y
... | _ , (z , zs) = cons (transPerm x zs) z

lemma-rem : Add a cs (a ∷ bs) → Perm cs bs
lemma-rem zero = reflPerm
lemma-rem (suc x) = cons reflPerm x

remPerm : Perm (a ∷ as) (a ∷ bs) → Perm as bs
remPerm  (cons permac addac ) = transPerm permac (lemma-rem addac)
