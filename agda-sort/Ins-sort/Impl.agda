
module Ins-sort.Impl where
open import Sort-rel
open import List
open import base




insert : {A : Set}{R : A → A → Set} → SortRel R →  A → List A → List A
insert R x [] = x ∷ []
insert R x (y ∷ ys) with SortRel.isDec R x y
... | yes _ = x ∷ y ∷ ys
... | no _ = y ∷ insert R x ys

ins-sort :{R : A → A → Set}→ SortRel R → List A → List A
ins-sort R [] = []
ins-sort R (x ∷ xs) = insert R x (ins-sort R xs)
