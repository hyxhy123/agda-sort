module Merge-sort.proof.Merge-sort-sorted where

open import base
open import List
open import LTree
open import Sort-rel
open import Sorted
open import Merge-sort.Impl

mutual
  ≤mergel :{R : A → A → Set}{x y : A}{xs ys : List A}(SR : SortRel R) → SR r x ≤all xs → SR r x ≤all ys → R x y → SR r x ≤all merge SR (y ∷ xs) ys
  ≤mergel {A} {R} {x} {y} {xs} {[]} SR x≤allxs [] x≤y = x≤y ∷ x≤allxs
  ≤mergel {A} {R} {x} {y} {[]} {x' ∷ ys} SR [] (x≤x' ∷ x≤allys) x≤y with SortRel.isDec SR y x'
  ... | yes _ = x≤y ∷ (x≤x' ∷ x≤allys)
  ... | no _ = x≤x' ∷ ≤mergel {A} {R} {x} {y} {[]} {ys} SR [] x≤allys x≤y
  ≤mergel {A} {R} {x} {y} {x' ∷ xs} {y' ∷ ys} SR (x≤x' ∷ x≤allxs) (x≤y' ∷ x≤allys) x≤y with SortRel.isDec SR y y'
  ... | no _ = x≤y' ∷ ≤mergel {A} {R} {x} {y} {x' ∷ xs} {ys} SR (x≤x' ∷ x≤allxs) x≤allys x≤y
  ... | yes _ with SortRel.isDec SR x' y'
  ... | yes _ = x≤y ∷ (x≤x' ∷ ≤merger {A} {R} {x} {y'} {xs} {ys}SR x≤allxs x≤allys x≤y')
  ... | no _ =  x≤y ∷ (x≤y' ∷ ≤mergel {A} {R} {x} {x'} {xs} {ys}SR x≤allxs x≤allys x≤x')
--SR r x ≤all merge SR xs (y' ∷ ys)

  ≤merger  :  {R : A → A → Set}{x y : A}{xs ys : List A}(SR : SortRel R) → SR r x ≤all xs → SR r x ≤all ys → R x y → SR r x ≤all merge SR xs (y ∷ ys)
  ≤merger {A} {R} {x} {y} {[]} {ys} SR x≤all[] x≤allys x≤y = x≤y ∷ x≤allys
  ≤merger  {A} {R} {x} {y} {x' ∷ xs} {[]} SR (x≤x' ∷ x≤allxs) [] x≤y with SortRel.isDec SR x' y
  ... | yes _ = x≤x' ∷ ≤merger  {A} {R} {x} {y} {xs} {[]}SR x≤allxs [] x≤y
  ... | no _ = x≤y ∷ (x≤x' ∷ x≤allxs)
  ≤merger  {A} {R} {x} {y} {x' ∷ xs} {y' ∷ ys} SR (x≤x' ∷ x≤allxs) (x≤y' ∷ x≤allys) x≤y with  SortRel.isDec SR x' y
  ... | yes _ = x≤x' ∷ ≤merger  {A} {R} {x} {y} {xs} {y' ∷ ys} SR x≤allxs (x≤y' ∷ x≤allys) x≤y
  ... | no _ with SortRel.isDec SR x' y'
  ... | yes _ = x≤y ∷ (x≤x' ∷ (≤merger  {A} {R}{x} {y'} {xs} {ys} SR x≤allxs x≤allys x≤y'))
  ... | no _  = x≤y ∷ (x≤y' ∷ ≤mergel {A} {R} {x} {x'} {xs} {ys} SR x≤allxs x≤allys x≤x') 
--SR r x ≤all merge SR (x' ∷ xs) ys


merge-sorted-add : {R : A → A → Set}{n : A}{l1 l2 : List A}(SR : SortRel R) → SR Sorted l1 → SR Sorted l2 → SR r n ≤all l1 → SR r n ≤all l2  → SR r n ≤all merge SR l1 l2
merge-sorted-add {A} {R} {n} {[]} {ys} SR sx sy x≤allxs x≤allys = x≤allys
merge-sorted-add {A} {R} {n} {x ∷ xs} {[]} SR sx sy x≤allxs x≤allys = x≤allxs
merge-sorted-add {A} {R} {n} {x ∷ xs} {y ∷ ys} SR (cons x≤allxs sx) (cons y≤allys sy) (n≤x ∷ n≤allxs) (n≤y ∷ n≤allys) with SortRel.isDec SR x y
... | yes _ = n≤x ∷ ≤merger  {A} {R}{n} {y} {xs} {ys} SR n≤allxs n≤allys n≤y
... | no _ = n≤y ∷ ≤mergel {A} {R} {n} {x} {xs} {ys} SR n≤allxs n≤allys n≤x

merge-sorted :{R : A → A → Set}{l1 l2 : List A}(SR : SortRel R) → SR Sorted l1 → SR Sorted l2 → SR Sorted (merge SR l1 l2)
merge-sorted {A} {R} {[]} {ys} SR sx sy = sy
merge-sorted {A} {R} {x ∷ xs} {[]} SR sx sy = sx
merge-sorted {A} {R} {x ∷ xs} {y ∷ ys} SR (cons x≤allxs sx) (cons y≤allys sy) with SortRel.isDec SR x y
... | yes x≤y = cons (merge-sorted-add {A} {R} {x} {xs} {y ∷ ys} SR sx (cons y≤allys sy) x≤allxs (x≤y ∷ (≤→≤all SR x≤y  y≤allys))) (merge-sorted {A} {R} {xs} {y ∷ ys} SR sx (cons y≤allys sy))
...  | no ¬x≤y = cons (merge-sorted-add {A} {R} {y} {x ∷ xs} {ys} SR (cons x≤allxs sx) sy (y≤x ∷ ≤→≤all SR y≤x x≤allxs) y≤allys) (merge-sorted {A} {R} {x ∷ xs} {ys} SR (cons x≤allxs sx) sy)
  where y≤x = SortRel.¬≤ SR ¬x≤y

LTmerge-sorted : {R : A → A → Set}(SR : SortRel R)(t : LTree A) → SR Sorted (LTmerge SR t)
LTmerge-sorted SR nil = nil
LTmerge-sorted SR (leaf x) = cons [] nil
LTmerge-sorted SR (node x l r) = merge-sorted SR ( LTmerge-sorted SR l) (LTmerge-sorted SR r)


merge-sort-sorted :{R : A → A → Set}(SR : SortRel R)(l : List A) → SR Sorted (merge-sort SR l)
merge-sort-sorted SR l = LTmerge-sorted SR (List2LT l)
