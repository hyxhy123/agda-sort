module Ins-sort.proof.Ins-sort-perm where
open import base
open import List
open import Ins-sort.Impl
open import Permutation
open import Sort-rel

insert-perm : {R : A → A → Set}{SR : SortRel R}(x : A)(l : List A) →  Perm (insert SR x l) (x ∷ l)
insert-perm x [] = reflPerm
insert-perm {SR = SR} x (y ∷ l) with SortRel.isDec SR x y
... | yes _ = reflPerm
... | no _ = cons (insert-perm x l) (suc zero)


lemma-perm-perm : {x : A}{l1 l2 : List A}{R : A → A → Set}{SR : SortRel R} → Perm l1 l2 → Perm (insert SR x (l1)) (x ∷ l2)
lemma-perm-perm {A} {x} {l1} {l2} {R} {SR} p = transPerm (insert-perm x l1) (cons p zero)

ins-sort-perm : {R : A → A → Set}{SR : SortRel R} (l : List A) → Perm (ins-sort SR  l) l
ins-sort-perm [] = nil
ins-sort-perm (x ∷ l) = lemma-perm-perm {x = x} (ins-sort-perm l)
