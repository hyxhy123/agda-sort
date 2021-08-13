module Merge-sort.proof.Merge-sort-perm where

open import base
open import List
open import LTree
open import Sort-rel
open import Permutation
open import Merge-sort.Impl

merge-nil-l : {R : A → A → Set}(SR : SortRel R)(xs : List A) → Perm (merge SR xs []) xs 
merge-nil-l SR [] = nil
merge-nil-l SR (x ∷ xs) = reflPerm
mutual
  merge-perm::l : {R : A → A → Set}{n : A}(SR : SortRel R) (l r : List A)→  Perm (n ∷ merge SR l r) (merge SR (n ∷ l) r)
  merge-perm::l {A} {R} {n}SR [] [] = reflPerm
  merge-perm::l {A} {R} {n}SR (x ∷ l) [] = reflPerm
  merge-perm::l {A} {R} {n}SR [] (x ∷ r) with SortRel.isDec SR n x
  ... | yes _ = reflPerm
  ... | no _ = transPerm perm-assoc (perm-add (merge-perm::l SR [] r))
  merge-perm::l {A} {R} {n} SR (x ∷ xs) (y ∷ ys) with SortRel.isDec SR n y
  ... | yes _ = reflPerm
  ... | no _ with SortRel.isDec SR x y
  ... | yes _ =  transPerm (perm-add (perm-add (symPerm (merge-perm::r {A} {R} {y} SR xs ys)))) (symPerm (transPerm (perm-add (symPerm (merge-perm::l SR (x ∷ xs) ys)))(transPerm (perm-add (perm-add (symPerm (merge-perm::l {A} {R} {x} SR xs ys)))) (transPerm perm-assoc (transPerm (perm-add perm-assoc) reflPerm)))))
  ... | no _ = symPerm (transPerm (perm-add (symPerm (merge-perm::l SR (x ∷ xs) ys))) perm-assoc)



--Perm (n ∷ y ∷ merge SR (x ∷ xs) ys) (y ∷ merge SR (n ∷ x ∷ xs) ys)

  merge-perm::r : {R : A → A → Set}{n : A}(SR : SortRel R) (l r : List A)→  Perm (n ∷ merge SR l r) (merge SR l (n ∷ r))
  merge-perm::r {A} {R} {n} SR [] r = reflPerm
  merge-perm::r {A} {R} {n} SR (x ∷ xs) [] with SortRel.isDec SR x n
  ... | yes _ = symPerm (transPerm (symPerm (perm-add (merge-perm::r SR xs []))) (transPerm perm-assoc (perm-add (perm-add (merge-nil-l SR xs)))))
  ... | no _ = reflPerm
  merge-perm::r {A} {R} {n} SR (x ∷ xs) (y  ∷ ys) with SortRel.isDec SR x n
  ... | no _  = reflPerm
  ... | yes _ with SortRel.isDec SR x y
  ... | yes _ = transPerm (perm-add (perm-add (symPerm (merge-perm::r {A} {R} {y} SR xs ys)))) (symPerm (transPerm (perm-add (symPerm (merge-perm::r SR xs (y ∷ ys)))) (transPerm (perm-add (perm-add (symPerm (merge-perm::r {n = y} SR  xs ys)))) perm-assoc)))
  ... | no _ = transPerm (perm-add (perm-add (symPerm (merge-perm::l {n = x} SR xs ys)))) (symPerm (transPerm (perm-add (symPerm (merge-perm::r SR xs (y ∷ ys)))) (transPerm (perm-add (perm-add (symPerm (merge-perm::r {n = y} SR xs ys)))) (transPerm perm-assoc (perm-add perm-assoc)))))
 

merge-perm-l : {R : A → A → Set} (SR : SortRel R) (l1 l2 r : List A) → Perm l1 l2 → Perm (merge SR l1 r) (merge SR l2 r)
merge-perm-l SR [] [] r p = reflPerm
merge-perm-l SR (x ∷ xs) [] [] p = p
merge-perm-l SR (x ∷ xs) (y ∷ ys) [] p = p
merge-perm-l SR (x ∷ xs) ys (z ∷ zs) p with SortRel.isDec SR x z
... | yes _ = transPerm (perm-add (symPerm (merge-perm::r {n = z}SR xs zs))) (symPerm (transPerm (symPerm (merge-perm::r {n = z}SR ys zs)) (symPerm (transPerm perm-assoc (perm-add (transPerm (merge-perm::l {n = x }SR xs zs) (merge-perm-l SR (x ∷ xs) ys zs p)))))))
... | no _ = symPerm (transPerm (symPerm (merge-perm::r {n = z}SR ys zs)) (perm-add (merge-perm-l SR ys (x ∷ xs) zs (symPerm p))))



merge-perm-r : {R : A → A → Set} (SR : SortRel R) (l r1 r2 : List A) → Perm r1 r2 → Perm (merge SR l r1) (merge SR l r2)
merge-perm-r SR xs [] [] p = reflPerm
merge-perm-r SR [] (y ∷ ys) zs p = p
merge-perm-r SR (x ∷ xs) (y ∷ ys) zs p with SortRel.isDec SR x y
... | yes _ = symPerm (transPerm (symPerm (merge-perm::l {n = x}SR xs zs)) (perm-add (merge-perm-r SR xs zs (y ∷ ys) (symPerm p))) )
... | no _ = transPerm (perm-add (symPerm (merge-perm::l {n = x}SR  xs ys))) (transPerm perm-assoc (transPerm (perm-add (merge-perm::r SR xs ys)) (symPerm (transPerm (symPerm (merge-perm::l {n = x}SR xs zs)) (perm-add (merge-perm-r SR xs zs (y ∷ ys) (symPerm p)))) )))

--Perm (merge SR xs zs) (merge SR xs (y ∷ ys))


insert-perm :{R : A → A → Set}{n : A}(SR : SortRel R)(t : LTree A) →  Perm (n ∷ LTmerge SR t) (LTmerge SR (insert n t))
insert-perm {A} {R} {n} SR nil = cons nil zero
insert-perm {A} {R} {n} SR (leaf v) with SortRel.isDec SR n v 
... | yes _ = cons (cons nil zero) zero
...  | no _ = perm-assoc
insert-perm {A} {R} {n} SR (node yes l r) = transPerm (merge-perm::l SR (LTmerge SR l) (LTmerge SR r)) (merge-perm-l SR (n ∷ LTmerge SR l) (LTmerge SR (insert n l)) (LTmerge SR r) (insert-perm SR l))
insert-perm {A} {R} {n} SR (node no l r) = transPerm (merge-perm::r SR (LTmerge SR l) (LTmerge SR r)) (merge-perm-r SR (LTmerge SR l) (n ∷ LTmerge SR r) (LTmerge SR (insert n r)) (insert-perm SR r))



merge-sort-perm :{R : A → A → Set}(SR : SortRel R)(l : List A) → Perm l (LTmerge SR (List2LT l))
merge-sort-perm {A} {R} SR [] = nil
merge-sort-perm {A} {R} SR (x ∷ l) = transPerm (cons (merge-sort-perm SR l) zero) (insert-perm SR (List2LT l))
