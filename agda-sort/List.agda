module List where
infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A 

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (a ∷ as) = f a ∷ map f as

_++_ :  {A : Set} →  List A → List A → List A
[] ++ l2 = l2
(x ∷ l1) ++ l2 = x ∷ (l1 ++ l2)
