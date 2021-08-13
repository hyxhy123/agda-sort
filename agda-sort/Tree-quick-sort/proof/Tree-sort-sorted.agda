module Tree-quick-sort.proof.Tree-sort-sorted where

open import Sort-rel
open import List
open import BST
open import base
open import Sorted
open import Tree
open import Tree-quick-sort.Impl

insert-t≤ : {x y : A}{t : Tree A}{R : A → A → Set}(SR : SortRel R) → R x  y → SR r t t≤ y → SR r (tree-insert SR x t) t≤ y
insert-t≤ SR x≤y lnil = lcons x≤y lnil
insert-t≤ {x = x } {t = node l z r}SR x≤y (lcons  z≤y rt≤y) with SortRel.isDec SR x  z
... | yes _ = lcons z≤y rt≤y
... | no _ = lcons z≤y (insert-t≤ SR x≤y rt≤y)

insert-≤t : {x y : A}{t : Tree A}{R : A → A → Set}(SR : SortRel R) → R y x → SR r y ≤t t → SR r y ≤t (tree-insert SR x t)
insert-≤t SR y≤x rnil = rcons y≤x rnil
insert-≤t {x =  x} {t = node l z r } SR y≤x (rcons  y≤z y≤tl) with  SortRel.isDec SR x  z
... | yes _ = rcons y≤z (insert-≤t SR y≤x y≤tl)
... | no _ = rcons y≤z y≤tl

insert-bst : {t : Tree A}{R : A → A → Set}(SR : SortRel R)(x : A)  → SR BST t → SR BST (tree-insert SR x t)
insert-bst  SR x leafb = nodeb leafb leafb lnil rnil
insert-bst  SR x  (nodeb {x = y} lbst rbst lt≤y y≤tr) with SortRel.isDec SR x  y
... | yes x≤y = nodeb (insert-bst   SR x lbst) rbst (insert-t≤ SR x≤y lt≤y) y≤tr
... | no ¬x≤y = nodeb lbst (insert-bst   SR x rbst) lt≤y (insert-≤t SR (SortRel.¬≤ SR ¬x≤y) y≤tr)

treesort-bst : {R : A → A → Set}(SR : SortRel R) (l : List A) → SR BST (list2tree  SR l)
treesort-bst SR [] = leafb
treesort-bst SR (x ∷ l) = insert-bst SR x (treesort-bst SR l)

treesort-sorted : {R : A → A → Set}(SR : SortRel R) (l : List A) → SR Sorted (tree2list (list2tree SR l))
treesort-sorted SR  l = bst-sorted  SR (treesort-bst SR l)
