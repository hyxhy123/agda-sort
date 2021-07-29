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

refl≤ : {x : ℕ} → x ≤ x
refl≤ {zero} = z≤n
refl≤ {suc x} = s≤s (refl≤ {x})


trans≤ : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans≤ z≤n _ =  z≤n
trans≤ (s≤s x≤y) (s≤s y≤z) = s≤s (trans≤ x≤y y≤z)

data _≤all_ :  ℕ →  List ℕ → Set where
    []  : {x : ℕ} → x ≤all []
    _∷_ : {x y : ℕ}{ys : List ℕ} → x ≤ y → x ≤all ys → x ≤all (y ∷ ys)

data _all≤_ : List ℕ →  ℕ → Set where
    [] :  {x : ℕ} → [] all≤ x
    _∷_ : {x y : ℕ}{ys : List ℕ} → y ≤ x → ys all≤ x → (y ∷ ys) all≤ x 

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

insert-sorted : {x : ℕ}{li : List ℕ} → Sorted li → Sorted (insert x li)
insert-sorted {x} {[]} nil = cons [] nil
insert-sorted {x} {y ∷ ys} (cons (y≤allys) sorted) with x ≤? y
... | yes x≤y = cons (x≤y ∷ trans-sorted x≤y y≤allys) (cons y≤allys sorted)
... | no ¬x≤y = cons (insert-sorted-aux {x} {y} {ys} ¬x≤y y≤allys) (insert-sorted {x} {ys} sorted )

ins-sort-sorted : (l : List ℕ) → Sorted (ins-sort l)
ins-sort-sorted [] = nil
ins-sort-sorted (x  ∷ xs) = insert-sorted  (ins-sort-sorted  xs)

insert-perm : (x : ℕ)(l : List ℕ) →  Perm (insert x l) (x ∷ l)
insert-perm x [] = reflPerm
insert-perm x (y ∷ l) with x ≤? y
... | yes _ = reflPerm
... | no _ = cons (insert-perm x l) (suc zero)


lemma-perm-perm : {x : ℕ}{l1 l2 : List ℕ} → Perm l1 l2 → Perm (insert x (l1)) (x ∷ l2)
lemma-perm-perm {x} {l1} {l2} p = transPerm (insert-perm x l1) (cons p zero)

ins-sort-perm : (l : List ℕ) → Perm (ins-sort l) l
ins-sort-perm [] = nil
ins-sort-perm (x ∷ l) = lemma-perm-perm {x} (ins-sort-perm l)
















-- treesort
data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

tree2list : Tree A → List A
tree2list leaf = []
tree2list (node l v r) = (tree2list l) ++ (v ∷  (tree2list r))

tree-insert : ℕ → Tree ℕ → Tree ℕ
tree-insert n leaf = node leaf n leaf
tree-insert n (node l v r) with n ≤? v
... | yes _  = node (tree-insert n l) v r
... | no _ = node l v (tree-insert n r)

list2tree : List ℕ → Tree ℕ
list2tree [] = leaf
list2tree (x ∷ xs) = tree-insert x (list2tree xs)

treesort : List ℕ → List ℕ
treesort l = tree2list (list2tree l)

data _≤t_ : ℕ → Tree ℕ → Set where
 rnil : {x  : ℕ } → x ≤t leaf
 rcons : {x y : ℕ}{l r : Tree ℕ} → x ≤ y → x ≤t l → x ≤t (node l y r)

data _t≤_ : Tree ℕ → ℕ → Set where
 lnil : {x  : ℕ } → leaf t≤ x
 lcons : {x y : ℕ}{l r : Tree ℕ} → y ≤ x → r t≤ x → (node l y r) t≤ x

data BST : Tree ℕ → Set where
 leafb : BST leaf
 nodeb : {x : ℕ} {l r : Tree ℕ} → BST l → BST r → l t≤ x → x ≤t r → BST (node l x r)


≤→≤all : {x y : ℕ}{ys : List ℕ} → x ≤ y → y ≤all ys → x ≤all ys
≤→≤all {x} {y} {[]} x≤y y≤allys = []
≤→≤all {x} {y} {n ∷ ys} x≤y ( y≤n ∷ y≤allys) = trans≤ x≤y y≤n ∷ ≤→≤all{x} {y} {ys} x≤y y≤allys 

≤→all≤ :{x y : ℕ}{xs : List ℕ} → xs all≤ y → y ≤ x → xs all≤ y
≤→all≤ {x} {y} {[]} x≤y y≤allys = []
≤→all≤ {x} {y} {n ∷ ys}  ( n≤y ∷ ysall≤y) y≤x = n≤y ∷ ysall≤y 

++all≤ : {x y : ℕ}{xs ys : List ℕ} → y ≤ x → xs all≤ y → ys all≤ x → (xs ++ (y ∷ ys)) all≤ x
++all≤ y≤x [] ysall≤x = y≤x ∷ ysall≤x
++all≤ z≤x (y≤z ∷ ysall≤z ) zsall≤x = (trans≤ y≤z z≤x) ∷ (++all≤ z≤x ysall≤z zsall≤x)

++≤all : {x y : ℕ}{xs ys : List ℕ} → x ≤ y → x ≤all xs → y ≤all ys → x ≤all (xs ++ (y ∷ ys))
++≤all x≤y [] y≤allys = x≤y ∷ ≤→≤all x≤y y≤allys
++≤all x≤z (x≤y ∷ x≤allys) z≤allzs = x≤y ∷ (++≤all x≤z x≤allys z≤allzs)




++sorted : {x : ℕ}{xs ys : List ℕ} → xs all≤ x → x ≤all ys → Sorted xs → Sorted ys → Sorted (xs ++ (x ∷ ys))
++sorted [] [] _ _ = cons [] nil
++sorted {x} [] x≤allys nil sortedyys = cons x≤allys sortedyys
++sorted (y≤x ∷ ysall≤x) [] (cons y≤allys sortedys) nil = cons (++≤all y≤x y≤allys []) (++sorted ysall≤x [] sortedys nil)
++sorted (y≤x ∷ ysall≤x) x≤allzs (cons  y≤allys sortedys) sortedzs = cons (++≤all y≤x y≤allys x≤allzs) (++sorted ysall≤x x≤allzs sortedys sortedzs)


t≤→all≤ : {x : ℕ}{t : Tree ℕ} → BST t → t t≤ x → (tree2list t) all≤ x
t≤→all≤ leafb lnil = []
t≤→all≤ (nodeb lbst rbst lt≤x x≤tr) (lcons x≤y rt≤y) = ++all≤ x≤y (t≤→all≤ lbst lt≤x) (t≤→all≤ rbst rt≤y)

≤t→≤all : {x : ℕ}{t : Tree ℕ} → BST t → x ≤t t → x ≤all (tree2list t)
≤t→≤all leafb rnil = []
≤t→≤all (nodeb lbst rbst lt≤y y≤tr) (rcons x≤y x≤tl) = ++≤all x≤y (≤t→≤all lbst x≤tl) (≤t→≤all rbst y≤tr)





bst-sorted : {t : Tree ℕ} → BST t → Sorted (tree2list t)
bst-sorted leafb = nil
bst-sorted (nodeb lbst rbst lt≤x x≤tr) = ++sorted (t≤→all≤ lbst lt≤x) (≤t→≤all rbst x≤tr) (bst-sorted lbst) (bst-sorted rbst)







insert-t≤ : {x y : ℕ}{t : Tree ℕ} → x ≤ y → t t≤ y → (tree-insert x t) t≤ y
insert-t≤ x≤y lnil = lcons x≤y lnil
insert-t≤ {x } {t = node l z r}x≤y (lcons  z≤y rt≤y) with x ≤? z
... | yes _ = lcons z≤y rt≤y
... | no _ = lcons z≤y (insert-t≤ x≤y rt≤y)

insert-≤t : {x y : ℕ}{t : Tree ℕ} → y ≤ x → y ≤t t → y ≤t (tree-insert x t)
insert-≤t y≤x rnil = rcons y≤x rnil
insert-≤t {x} {t = node l z r } y≤x (rcons  y≤z y≤tl) with x ≤? z
... | yes _ = rcons y≤z (insert-≤t y≤x y≤tl)
... | no _ = rcons y≤z y≤tl


insert-bst : {t : Tree ℕ}(x : ℕ) → BST t → BST (tree-insert x t)
insert-bst x leafb = nodeb leafb leafb lnil rnil
insert-bst x (nodeb {x = y} lbst rbst lt≤y y≤tr) with x ≤? y
... | yes x≤y = nodeb (insert-bst x lbst) rbst (insert-t≤ x≤y lt≤y) y≤tr
... | no ¬x≤y = nodeb lbst (insert-bst x rbst) lt≤y (insert-≤t (¬≤ ¬x≤y) y≤tr)

treesort-bst : (l : List ℕ) → BST (list2tree l)
treesort-bst [] = leafb
treesort-bst (x ∷ l) = insert-bst x (treesort-bst l)

treesort-sorted : (l : List ℕ) → Sorted (tree2list (list2tree l))
treesort-sorted  l = bst-sorted  (treesort-bst l)

lemma-add++ :  Add a as cs → Add a (as ++ bs) (cs ++ bs)
lemma-add++  zero = zero
lemma-add++ (suc x) = suc (lemma-add++ x)

lemma-add::++ : {x : ℕ}{xs : List ℕ} → Add a cs (x ∷ xs) → Add a (cs ++ bs) (x ∷ (xs ++ bs))
lemma-add::++ zero = zero
lemma-add::++ {a} {as} {bs} {x}  (suc m) = suc (lemma-add++  m)

++perm-aux : Perm as [] → Perm (as ++ bs ) bs
++perm-aux nil = reflPerm

++perm : {as bs cs : List ℕ} → Perm as cs → Perm (as ++ bs) (cs ++ bs)
++perm {as} {bs} {[]} m = ++perm-aux m
++perm {.(_ ∷ _)} {bs} {x ∷ xs} (cons m x₁) = cons (++perm m) (lemma-add::++ x₁)


lemma-add++l :   Add a (as ++ bs) (as ++ (a ∷ bs))
lemma-add++l {a} {[]} {bs} = zero
lemma-add++l {a} {x ∷ as} {bs} = suc lemma-add++l

lemma-perm::++ : Perm (a ∷ (as ++ bs)) (as ++ (a ∷ bs))
lemma-perm::++ {a} {as} {bs} = cons (reflPerm) lemma-add++l

lemma-perm++l : Perm bs cs → Perm (as ++ bs) (as ++ cs)
lemma-perm++l {bs} {cs} {[]} x = x
lemma-perm++l {bs} {cs} {x₁ ∷ as} x = cons (lemma-perm++l x) zero

perm-assoc : Perm (a ∷ b ∷ as) (b ∷ a ∷ as)
perm-assoc {a} {b} {as} = cons (cons reflPerm zero) (suc zero)

perm-add : Perm as bs → Perm (a ∷ as) (a ∷ bs)
perm-add  nil = cons nil zero
perm-add  p = cons p zero


tree-insert-perm : (x : ℕ) → (t : Tree ℕ) → Perm (x ∷ tree2list t) (tree2list (tree-insert x t)) 
tree-insert-perm x leaf = cons nil zero
tree-insert-perm x (node l v r) with x ≤? v
... | yes x≤v = ++perm (tree-insert-perm x l)
... | no ¬x≤v = transPerm  (lemma-perm::++ {as = tree2list l } ) (lemma-perm++l  {as = tree2list l}(transPerm perm-assoc   (perm-add (tree-insert-perm x r))))

treesort-perm : (l : List ℕ) → Perm l (tree2list (list2tree l) ) 
treesort-perm [] = nil
treesort-perm (x ∷ l) = transPerm (cons (treesort-perm l) zero) (tree-insert-perm x (list2tree l))
