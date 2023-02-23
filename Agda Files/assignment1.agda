data ⊥ : Set where

data ⊤ : Set where
    tt : ⊤

exFalso : ⊥ → Set
exFalso ()

data _∧_ : Set → Set → Set where
    _,_ : {A B : Set} → A → B → A ∧ B

proj1 : {A B : Set} → A ∧ B → A
proj1 (a , b) = a

proj2 : {A B : Set} → A ∧ B → B
proj2 (a , b) = b

data _∨_ : Set → Set → Set where
    inj1 : {A B : Set} → A → A ∨ B
    inj2 : {A B : Set} → B → A ∨ B

¬ : Set → Set
¬ = λ A → (A → ⊥)

q4+ : (P Q : Set) → ((¬ P) ∧ (¬ Q)) → ¬ (P ∨ Q)
q4+ P Q h (inj1 x) = proj1 h x
q4+ P Q h (inj2 x) = proj2 h x

q4- : (P Q : Set) → ¬ (P ∨ Q) → ((¬ P) ∧ (¬ Q))
q4- P Q h = (λ x → h (inj1 x)) , λ x → h (inj2 x)

q3 : ∀ (P Q : Set) → ((P → Q) ∧ ¬ Q) → ¬ P
q3 P Q h p = (proj2 h) ((proj1 h) p)

Rel : Set → Set₁
Rel A = A → A → Set

isRefl : {A : Set} → Rel A → Set 
isRefl R = ∀ x → R x x 

isSymm : {A : Set} → Rel A → Set 
isSymm R = ∀ x y → R x y → R y x

isTran : {A : Set} → Rel A → Set 
isTran R = ∀ x y z → R x y → R y z → R x z 

isEuclidean : {A : Set} → Rel A → Set 
isEuclidean R = ∀ x y z → R x z → R y z → R x y 

lemma1 : {A : Set} → (R : Rel A) → isEuclidean R ∧ isRefl R → isSymm R
lemma1 R ER = λ x y x₁ → proj1 ER y x y (proj2 ER y) x₁

EuclidIsEq : {A : Set} → (R : Rel A) → isEuclidean R ∧ isRefl R → isSymm R ∧ isTran R 
EuclidIsEq R ER = (lemma1 R ER) , (λ x y z x₁ x₂ → proj1 ER x z y x₁ (lemma1 R ER y z x₂))

