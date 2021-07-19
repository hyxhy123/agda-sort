open import lib24

variable a b : ℕ
variable as bs cs as' bs' cs' cs'' : List ℕ

data Add : ℕ → List ℕ → List ℕ → Set where
  zero : Add a as (a ∷ as) 
  suc : Add a as bs → Add a (b ∷ as) (b ∷ bs)

data Perm : List ℕ → List ℕ → Set where
  nil : Perm  [] []
  cons : Perm as cs → Add a cs bs → Perm (a ∷ as) bs

-- easy
reflPerm : Perm as as
reflPerm { [] }   = nil
reflPerm {x ∷ xs } = cons ( reflPerm {xs} ) zero
-- hard, need some lemmas

lemma-add : Add a bs cs → Perm bs as → Perm cs (a ∷ as)
lemma-add zero  p = cons p zero
lemma-add (suc x) (cons p add) = cons (lemma-add x p) (suc add)

symPerm : Perm as bs → Perm bs as
symPerm nil = nil
symPerm (cons permab add) = lemma-add add (symPerm permab)

lemma-assoc : Add a as bs → Add b bs cs → Ex (List ℕ) (λ bs' → (Add b as bs') × (Add a bs' cs))
lemma-assoc x zero = _ , (zero , (suc x))
lemma-assoc zero (suc y) = _ , (y , zero)
lemma-assoc (suc x) (suc y) with lemma-assoc x y
... | _ , (x' , y') = _ , (suc x' , suc y')

--need the third list bs'
Perm→Add×Perm  :  Add a bs cs  →  Perm cs cs'  → (Ex  (List ℕ) (λ bs' → Add a bs' cs' × Perm bs bs') )
Perm→Add×Perm  zero (cons x₁ x)  = (_ , (x  , x₁))
Perm→Add×Perm  (suc x) (cons x₁ x₂) with Perm→Add×Perm  x x₁
... | ys , (z , zs ) with lemma-assoc z x₂
... | ys' , ( z' , zs' ) = ys' , (zs' , (cons zs z'))

transPerm : Perm as bs → Perm bs cs → Perm as cs
transPerm nil nil = nil
transPerm (cons x x₁) y with Perm→Add×Perm  x₁ y
... | _ , (z , zs) = cons (transPerm x zs) z

lemma-rem : Add a cs (a ∷ bs) → Perm cs bs
lemma-rem zero = reflPerm
lemma-rem (suc x) = cons reflPerm x

remPerm : Perm (a ∷ as) (a ∷ bs) → Perm as bs
remPerm  (cons permac addac ) = transPerm permac (lemma-rem addac)

-- (l : List ℕ) → Perm l (sort l)

-- prove sorted for treesort
-- prove properties of Perm
-- prove perm for insertion-sort and tree-sort

-- milestone? => email (but also if you are stuck)

-- quick-sort, merge-sort
-- not structurally recursive
-- quick-sort is basically tree-sort (fusion)
-- modified tree-sort which is related to merge-sort
-- can we verify quick-sort and merge-sort using the versions on trees + fusion?

data _≤_ : ℕ → ℕ → Set where
  z≤n :  {x : ℕ} → zero ≤ x
  s≤s :  {x y : ℕ} → x ≤ y → suc x ≤ suc y

--data AllList  : (P : ℕ → Set ) → List ℕ → Set  where
--  nil : (P : ℕ → Set ) → AllList P []
--  cons : {a : ℕ}{P : ℕ → Set }{l : List ℕ} → P a → AllList P l → AllList P (a ∷ l)

trans≤ : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans≤ z≤n _ =  z≤n
trans≤ (s≤s x≤y) (s≤s y≤z) = s≤s (trans≤ x≤y y≤z)

data _≤all_ (x : ℕ) : List ℕ → Set where
    []  : x ≤all []
    _∷_ : {y : ℕ}{ys : List ℕ} → x ≤ y → x ≤all ys → x ≤all (y ∷ ys)

data Sorted : List ℕ → Set where
 nil : Sorted []
 cons : {a : ℕ}{l : List ℕ} →  a ≤all l   → Sorted l → Sorted (a ∷ l)
 

¬s≤s : {x y : ℕ} → ¬ (x ≤ y) → ¬ (suc x ≤ suc y)
¬s≤s ¬x≤y (s≤s x≤y) = ¬x≤y x≤y

_≤?_ : (x y : ℕ )→ Dec (x ≤ y )
zero ≤? y = yes z≤n 
(suc x) ≤?  zero = no λ ()
(suc x) ≤?  (suc y) with x ≤? y
... | yes x≤y = yes (s≤s x≤y)
... | no ¬x≤y = no (¬s≤s ¬x≤y)

insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys)  with x ≤? y
... | yes _ = x ∷ y ∷ ys
... | no _ = y ∷ insert x ys

ins-sort : List ℕ → List ℕ
ins-sort [] = []
ins-sort (x ∷ xs) = insert x (ins-sort xs)

{-
data _≤all_ (x : ℕ) : List ℕ → Set where
    []  : x ≤all []
    _∷_ : {y : ℕ}{ys : List ℕ} → x ≤ y → x ≤all ys → x ≤all (y ∷ ys)

data Sorted : List ℕ → Set where
 nil : Sorted []
 cons : {a : ℕ}{l : List ℕ} →  a ≤all l   → Sorted l → Sorted (a ∷ l)
 
-}
trans-sorted : {x y : ℕ}{ys : List ℕ} → x ≤ y → y ≤all ys → x ≤all ys
trans-sorted {x} {y} {[]} x≤y y≤allys = []
trans-sorted {x} {y} {n ∷ ys} x≤y ( y≤n ∷ y≤allys) = trans≤ x≤y y≤n ∷ trans-sorted {x} {y} {ys} x≤y y≤allys 

total≤ : (x y : ℕ) → (x ≤ y) ∨ (y ≤ x)
total≤ zero y = inj₁ z≤n
total≤ (suc x) zero = inj₂ z≤n
total≤ (suc x) (suc y) with total≤ x y
... | inj₁ x≤y = inj₁ (s≤s x≤y)
... | inj₂ y≤x = inj₂ (s≤s y≤x)

¬≤ : {x y : ℕ} → ¬ (x ≤ y) → y ≤ x
¬≤ {x} {y} ¬x≤y with total≤ x y
... | inj₁ x≤y = case⊥ (¬x≤y x≤y)
... | inj₂ y≤x = y≤x

insert-sorted-aux : {x y : ℕ}{li : List ℕ} → ¬ (x ≤ y) → y ≤all li → y ≤all (insert x li)
insert-sorted-aux {x} {y} {[]} ¬x≤y y≤allys = ¬≤ ¬x≤y ∷ []
insert-sorted-aux {x} {y} {n ∷ ys} ¬x≤y (y≤n ∷ y≤allys) with x ≤? n
... | yes x≤n = (¬≤ ¬x≤y) ∷ (y≤n ∷ y≤allys)
... | no ¬x≤n = y≤n ∷ (insert-sorted-aux {x} {y} {ys} ¬x≤y  y≤allys)

insert-perm : (x : ℕ)(l : List ℕ) →  Perm (insert x l) (x ∷ l)
insert-perm x [] = reflPerm
insert-perm x (x₁ ∷ l) = {!!}

ins-sort-perm : (l : List ℕ) → Perm (ins-sort l) l
ins-sort-perm [] = nil
ins-sort-perm (x ∷ l) = {!!}

