module Tree-quick-sort.proof.Tree-sort-perm where
open import Permutation
open import base
open import Tree-quick-sort.Impl
open import List
open import Tree
open import Sort-rel

lemma-add++ :  Add a as cs → Add a (as ++ bs) (cs ++ bs)
lemma-add++  zero = zero
lemma-add++ (suc x) = suc (lemma-add++ x)

lemma-add::++ : {x : A}{xs : List A} → Add a cs (x ∷ xs) → Add a (cs ++ bs) (x ∷ (xs ++ bs))
lemma-add::++ zero = zero
lemma-add::++ {a} {as} {bs} {x}  (suc m) = suc (lemma-add++  m)

++perm-aux : Perm as [] → Perm (as ++ bs ) bs
++perm-aux nil = reflPerm

++perm : {as bs cs : List A} → Perm as cs → Perm (as ++ bs) (cs ++ bs)
++perm {t}{as} {bs} {[]} m = ++perm-aux m
++perm {t}{.(_ ∷ _)} {bs} {x ∷ xs} (cons m x₁) = cons (++perm m) (lemma-add::++ x₁)

lemma-add++l : Add a (as ++ bs) (as ++ (a ∷ bs))
lemma-add++l {t} {a} {[]} {bs} = zero
lemma-add++l {t} {a} {x ∷ as} {bs} = suc lemma-add++l

lemma-perm::++ : Perm (a ∷ (as ++ bs)) (as ++ (a ∷ bs))
lemma-perm::++ {a} {as} {bs} = cons (reflPerm) lemma-add++l

lemma-perm++l : Perm bs cs → Perm (as ++ bs) (as ++ cs)
lemma-perm++l {t} {bs} {cs} {[]} x = x
lemma-perm++l {t} {bs} {cs} {x₁ ∷ as} x = cons (lemma-perm++l x) zero

perm-assoc : Perm (a ∷ b ∷ as) (b ∷ a ∷ as)
perm-assoc {a} {b} {as} = cons (cons reflPerm zero) (suc zero)

perm-add : Perm as bs → Perm (a ∷ as) (a ∷ bs)
perm-add  nil = cons nil zero
perm-add  p = cons p zero


tree-insert-perm : {R : A → A → Set}(SR : SortRel R)(x : A) → (t : Tree A) → Perm (x ∷ tree2list t) (tree2list (tree-insert SR x t)) 
tree-insert-perm SR x leaf = cons nil zero
tree-insert-perm SR x (node l v r) with SortRel.isDec SR x  v
... | yes x≤v = ++perm  (tree-insert-perm SR x l)
... | no ¬x≤v = transPerm  (lemma-perm::++ {as = tree2list l } ) (lemma-perm++l  {as = tree2list l}(transPerm perm-assoc   (perm-add (tree-insert-perm SR x r))))

treesort-perm : {R : A → A → Set}(SR : SortRel R)(l : List A) → Perm l (tree2list (list2tree SR l) ) 
treesort-perm SR [] = nil
treesort-perm SR (x ∷ l) = transPerm (cons (treesort-perm SR l) zero) (tree-insert-perm SR x (list2tree SR l))


