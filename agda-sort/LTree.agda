module LTree where
open import base
open import List
data Balanced : Set where
 yes : Balanced 
 no : Balanced
 
data LTree (A : Set) :  Set where
  nil : LTree A 
  leaf :  A → LTree A 
  node : Balanced →  LTree A  → LTree A  → LTree A 

insert : A →  LTree A  → LTree A 
insert x nil = leaf x
insert x (leaf v) = node yes (leaf x) (leaf v)
insert x (node yes l r) = node no (insert x l) r
insert x (node no l r) = node yes l (insert x r)

List2LT : List A → LTree A
List2LT [] = nil
List2LT (x ∷ xs) = insert x (List2LT xs)
