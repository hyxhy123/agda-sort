module Tree-quick-sort.Impl where
open import base
open import Sort-rel
open import Tree
open import List

tree-insert :{R : A → A → Set}(SR : SortRel R) →  A → Tree A → Tree A
tree-insert SR n leaf = node leaf n leaf
tree-insert SR n (node l v r) with SortRel.isDec SR n v
... | yes _  = node (tree-insert SR n l) v r
... | no _ = node l v (tree-insert SR n r)

list2tree : {R : A → A → Set}(SR : SortRel R) → List A → Tree A
list2tree SR [] = leaf
list2tree SR (x ∷ xs) = tree-insert SR x (list2tree SR xs)

treesort : {R : A → A → Set}(SR : SortRel R) → List A → List A
treesort SR l = tree2list (list2tree SR l)
