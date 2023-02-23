data ⊥ : Set where

exFalso : ⊥ → Set
exFalso ()

data ⊤ : Set where
    tt : ⊤

¬ : Set → Set
¬ = λ A → (A → ⊥)

Ax1 : {A B : Set} → A → B → A
Ax1 a b = a 

Ax2 : {A B C : Set} → (A → (B → C)) → ((A → B) → (A → C))
Ax2 = λ x x₁ x₂ → x x₂ (x₁ x₂)

Ax3 : {A B : Set} → ((¬ B) → (¬ A)) → ((¬ B) → A) → B
Ax3 = {!   !}

lemma1 : {A : Set} → A → A
lemma1 a = a

lemma2 : (B : Set) → (¬ B → B) → B
lemma2 B = {!  !}

lemma3 : {A B C : Set} → (A → (B → C)) → (A → B)-> A → C
lemma3 = Ax2

lemma4 : {A B C : Set} → (A → ((B → A) → C)) → A → C
lemma4 = λ x x₁ → Ax2 x Ax1 x₁

lemma5 : {A B : Set} → B → (A → B)
lemma5 = Ax1

lemma6 : {A B C : Set} -> (A → (B → C)) → B → (A → C)
lemma6 = λ x x₁ x₂ → x x₂ x₁

lemma7 : {A B C : Set} → (A → (B → C)) → (B → (A → C))
lemma7 = λ x x₁ x₂ → x x₂ x₁

lemma8 : {A B C : Set} → (A → B) → (B → C) → A → C
lemma8 = λ x x₁ x₂ → x₁ (x x₂)

lemma9 : {P Q R : Set} → (P → R) → P → Q → R
lemma9 = λ x x₁ x₂ → x x₁

lemma10 : {A B : Set} → ((¬ B) → (¬ A)) → (A → B)
lemma10 ¬b¬a a = {!   !}

lemma11 : {B : Set} → (¬ (¬ B)) → B
lemma11 = λ x → {!   !}

lemma12 : {B : Set} → B → (¬ (¬ B))
lemma12 = λ x x₁ → x₁ x

lemma13 : {}