module Sort-rel where
open import base

record SortRel {A : Set}(R : A → A → Set) : Set where
  field
    isDec : (a b : A) → Dec (R a b)
    trans : {a b c : A} → R a b → R b c → R a c
    ¬≤ : {a b : A } → ¬ (R a b) → R b a
