module Merge-sort.proof.Merge-sort-perm where

open import base
open import List
open import LTree
open import Sort-rel
open import Permutation
open import Merge-sort.Impl



merge-sort-sorted :{R : A → A → Set}(SR : SortRel R)(l : List A) → Perm l (merge-sort SR l)
merge-sort-sorted SR l = ?
