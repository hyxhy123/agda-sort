module BST where
open import base
open import Tree
open import Sort-rel
open import List
open import Sorted
data _r_≤t_ {R : A → A → Set} (SR : SortRel R) : A → Tree A → Set where
 rnil : {x  : A } → SR r x ≤t leaf
 rcons : {x y : A}{l r : Tree A} → R x y → SR r x ≤t l → SR r x ≤t (node l y r)

data _r_t≤_ {R : A → A → Set} (SR : SortRel R) : Tree A → A → Set where
 lnil : {x  : A } → SR r leaf t≤ x
 lcons : {x y : A}{l r : Tree A} → R y x → SR r r t≤ x → SR r (node l y r) t≤ x

data _BST_ {R : A → A → Set} (SR : SortRel R): Tree A → Set where
 leafb : SR BST leaf
 nodeb : {x : A} {l r : Tree A} → SR BST l → SR BST r → SR r l t≤ x → SR r x ≤t r → SR BST (node l x r)



t≤→all≤ : {x : A}{t : Tree A}{R : A → A → Set} (SR : SortRel R) → SR BST t → SR r t t≤ x →  SR r (tree2list  t) all≤ x
t≤→all≤ SR leafb lnil = []
t≤→all≤ SR (nodeb lbst rbst lt≤x x≤tr) (lcons x≤y rt≤y) = ++all≤ SR x≤y (t≤→all≤ SR lbst lt≤x) (t≤→all≤ SR rbst rt≤y)

≤t→≤all : {x : A}{t : Tree A}{R : A → A → Set} (SR : SortRel R) → SR BST t → SR r x ≤t t → SR r x ≤all (tree2list t)
≤t→≤all SR leafb rnil = []
≤t→≤all SR (nodeb lbst rbst lt≤y y≤tr) (rcons x≤y x≤tl) = ++≤all SR x≤y (≤t→≤all SR lbst x≤tl) (≤t→≤all SR rbst y≤tr)

bst-sorted : {t : Tree A}{R : A → A → Set} (SR : SortRel R)  → SR BST t → SR Sorted (tree2list t)
bst-sorted SR leafb = nil
bst-sorted SR (nodeb lbst rbst lt≤x x≤tr) = ++sorted SR (t≤→all≤ SR lbst lt≤x) (≤t→≤all SR rbst x≤tr) (bst-sorted SR lbst) (bst-sorted SR rbst)
