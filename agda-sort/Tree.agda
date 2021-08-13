module Tree where
open import base
open import List
open import Sort-rel
open import Sorted
data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A


tree2list : Tree A → List A
tree2list leaf = []
tree2list (node l v r) = (tree2list l) ++ (v ∷  (tree2list r))


