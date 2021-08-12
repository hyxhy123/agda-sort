module Merge-sort.Impl where
open import base

open import List
open import LTree
open import Sort-rel




merge : {R : A → A → Set}(SR : SortRel R) → List A → List A → List A
merge SR [] ys = ys
merge SR (x ∷ xs) [] = x ∷ xs
merge SR (x ∷ xs) (y ∷ ys) with SortRel.isDec SR x y 
... | yes _ = x ∷ (merge SR xs (y ∷ ys))
... | no _ = y ∷ merge SR (x ∷ xs) ys

LTmerge : {R : A → A → Set}(SR : SortRel R) → LTree A → List A
LTmerge SR nil = []
LTmerge SR (leaf x) = x ∷ []
LTmerge SR (node b l r) = merge SR (LTmerge SR l) (LTmerge SR r)

merge-sort :{R : A → A → Set}(SR : SortRel R) → List A → List A
merge-sort SR l = LTmerge SR (List2LT l)


