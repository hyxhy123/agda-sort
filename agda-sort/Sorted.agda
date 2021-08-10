module Sorted where
open import List
open import base
open import Sort-rel
data _r_≤all_ {A : Set}{R : A → A → Set}(SR : SortRel R) : A →  List A  →   Set where
    []  : {x : A} → SR r x ≤all []   
    _∷_ : {x y : A}{ys : List A} → R x y →  SR r x ≤all ys    → SR r x ≤all (y ∷ ys) 

data _r_all≤_ {A : Set}{R : A → A → Set}(SR : SortRel R) :   List A →  A →  Set where
    [] :  {x : A} → SR r [] all≤ x  
    _∷_ : {x y : A}{ys : List A} → R y x → SR r ys all≤ x  → SR r (y ∷ ys) all≤ x 

data _Sorted_ {A : Set} {R : A → A → Set}(SR : SortRel R) : List A  → Set  where
 nil :   SR Sorted [] 
 cons : {a : A}{l : List A} → SR  r a ≤all l   → SR  Sorted l  → SR  Sorted (a ∷ l)



≤→≤all : {x y : A}{ys : List A}{R : A → A → Set}(SR : SortRel R) → R x y → SR r y ≤all ys → SR r x ≤all ys
≤→≤all {A} {x} {y} {[]} {R} SR x≤y y≤allys = []
≤→≤all {A} {x} {y} {n ∷ ys} {R} SR x≤y (y≤n ∷ y≤allys) = (SortRel.trans  SR ) x≤y y≤n ∷ ( ≤→≤all {A} {x} {y} { ys} {R} SR x≤y y≤allys )

≤→all≤ :{x y : A}{xs : List A}{R : A → A → Set}(SR : SortRel R) → SR r xs all≤ y → R y x → SR r xs all≤ y
≤→all≤ {A} {x} {y} {[]} {R} SR x≤y y≤allys = []
≤→all≤ {A} {x} {y} {n ∷ ys} {R} SR  ( n≤y ∷ ysall≤y) y≤x = n≤y ∷ ysall≤y

++all≤ : {x y : A}{xs ys : List A}{R : A → A → Set}(SR : SortRel R) → R y  x → SR r xs all≤ y → SR r ys all≤ x → SR r (xs ++ (y ∷ ys)) all≤ x
++all≤ SR y≤x [] ysall≤x = y≤x ∷ ysall≤x
++all≤ SR z≤x (y≤z ∷ ysall≤z ) zsall≤x = (SortRel.trans SR y≤z z≤x) ∷ (++all≤ SR z≤x ysall≤z zsall≤x)

++≤all : {x y : A}{xs ys : List A}{R : A → A → Set}(SR : SortRel R) → R x  y → SR r x ≤all xs → SR r y ≤all ys → SR r x ≤all (xs ++ (y ∷ ys))
++≤all SR x≤y [] y≤allys = x≤y ∷ ≤→≤all SR x≤y y≤allys
++≤all SR x≤z (x≤y ∷ x≤allys) z≤allzs = x≤y ∷ (++≤all SR x≤z x≤allys z≤allzs)


++sorted : {x : A}{xs ys : List A} {R : A → A → Set}(SR : SortRel R) → SR r xs all≤ x → SR r x ≤all ys → SR Sorted xs → SR Sorted ys → SR  Sorted (xs ++ (x ∷ ys))
++sorted SR [] [] _ _ = cons [] nil
++sorted {x} SR [] x≤allys nil sortedyys = cons x≤allys sortedyys
++sorted SR (y≤x ∷ ysall≤x) [] (cons y≤allys sortedys) nil = cons (++≤all SR y≤x y≤allys []) (++sorted SR ysall≤x [] sortedys nil)
++sorted SR (y≤x ∷ ysall≤x) x≤allzs (cons  y≤allys sortedys) sortedzs = cons (++≤all SR y≤x y≤allys x≤allzs) (++sorted SR ysall≤x x≤allzs sortedys sortedzs)
