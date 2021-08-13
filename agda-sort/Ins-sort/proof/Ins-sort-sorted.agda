module Ins-sort.proof.ins-sort-sorted where
open import base
open import Sort-rel
open import List
open import Sorted
open import Ins-sort.Impl

insert-sorted-aux : {x y : A}{li : List A}{R : A → A → Set}{SR : SortRel R} → ¬ (R x  y) → SR r y ≤all li → SR r y ≤all (insert SR x li)
insert-sorted-aux {A} {x} {y} {[]} {R} {SR} ¬x≤y [] = SortRel.¬≤ SR ¬x≤y ∷ []
insert-sorted-aux {A} {x} {y} {n ∷ ys} {R} {SR} ¬x≤y (y≤n ∷ y≤allys) with SortRel.isDec SR x n
... | yes _ = SortRel.¬≤ SR ¬x≤y ∷ y≤n ∷ y≤allys
... | no _ = y≤n ∷ (insert-sorted-aux {A} {x} {y} { ys} {R} {SR} ¬x≤y y≤allys )



insert-sorted : {A : Set}{R : A → A → Set}{SR : SortRel R}{x : A}{li : List A} → SR Sorted li → SR Sorted (insert SR x li)
insert-sorted {x = x} {li = []} nil = cons [] nil
insert-sorted {R = R}{SR = SR}{x = x} {li = y ∷ ys} (cons (y≤allys) sorted) with SortRel.isDec SR x y
... | yes x≤y = cons (x≤y ∷ ≤→≤all SR x≤y y≤allys) (cons y≤allys sorted)
... | no ¬x≤y = cons (insert-sorted-aux  {x = x} {y = y} {li = ys} ¬x≤y y≤allys) (insert-sorted {x = x} {li = ys} sorted )

ins-sort-sorted : {R : A → A → Set}{SR : SortRel R} (l : List A)  → SR Sorted (ins-sort SR  l)
ins-sort-sorted [] = nil
ins-sort-sorted (x  ∷ xs) = insert-sorted  (ins-sort-sorted  xs)
