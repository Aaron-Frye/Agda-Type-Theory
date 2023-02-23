data Nat : Set where
    zero : Nat
    suc : Nat → Nat

_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = suc (x + y)

data _≤_ : Nat → Nat → Set where
    zero≤ : (x : Nat) → zero ≤ x
    mono≤ : (x y : Nat) → x ≤ y → suc x ≤ suc y

data _∨_ : Set → Set → Set where
    inj1 : {A B : Set} → A → A ∨ B
    inj2 : {A B : Set} → B → A ∨ B

lemma1 : (x : Nat) → x ≤ suc x
lemma1 zero = zero≤ (suc zero)
lemma1 (suc x) = mono≤ x (suc x) (lemma1 x)

lemma2 : (x y : Nat) → x ≤ y → (zero + x) ≤ (zero + y)
lemma2 x y lt = lt

lemma3 : (x y : Nat) → x ≤ y → (x + zero) ≤ (y + zero)
lemma3 .zero y (zero≤ .y) = zero≤ (y + zero)
lemma3 .(suc x) .(suc y) (mono≤ x y lt) = mono≤ (x + zero) (y + zero) (lemma3 x y lt)

isReflexive : (x : Nat) → x ≤ x
isReflexive zero = zero≤ zero
isReflexive (suc x) = mono≤ x x (isReflexive x)

isTransitive : (x y z : Nat) → x ≤ y → y ≤ z → x ≤ z
{-isTransitive .zero y z (zero≤ .y) yz = zero≤ z
isTransitive .(suc x) .(suc y) .(suc y₁) (mono≤ x y xy) (mono≤ .y y₁ yz) = mono≤ x y₁ (isTransitive x y y₁ xy yz)-}
isTransitive .zero .zero z (zero≤ .zero) (zero≤ .z) = zero≤ z
isTransitive .zero (suc y) (suc z) (zero≤ .(suc y)) (mono≤ y z yz) = zero≤ (suc z)
isTransitive .(suc x) (suc y) (suc z) (mono≤ x .y xy) (mono≤ y z yz) = mono≤ x z (isTransitive x y z xy yz)

lemma4 : (x y : Nat) → x ≤ (x + y)
lemma4 zero y = zero≤ y
lemma4 (suc x) y = mono≤ x (x + y) (lemma4 x y)

lemma7 : (x y : Nat) → x ≤ (y + x)
lemma7 x zero = isReflexive x
lemma7 x (suc y) = {!   !}

lemma6 : (x y z : Nat) → (x ≤ y) ∨ (x ≤ z) → x ≤ (y + z)
lemma6 .zero y z (inj1 (zero≤ .y)) = {!   !}
lemma6 .(suc x) .(suc y) z (inj1 (mono≤ x y x₁)) = mono≤ x (y + z) (lemma6 x y z (inj1 x₁))
lemma6 .zero y z (inj2 (zero≤ .z)) = {!   !}
lemma6 .(suc x) zero .(suc y₁) (inj2 (mono≤ x y₁ x₁)) = {!   !}
lemma6 .(suc x) (suc y) .(suc y₁) (inj2 (mono≤ x y₁ x₁)) = mono≤ x (y + suc y₁) (lemma6 x y (suc y₁) (inj2 {!   !}))

≤cong1 : (x y y' : Nat) → y ≤ y' → (x + y) ≤ (x + y')
≤cong1 zero y y' yy = yy
≤cong1 (suc x) y y' yy = mono≤ (x + y) (x + y') (≤cong1 x y y' yy)

{-
≤cong2 : (x x' y : Nat) → x ≤ x' → (x + y) ≤ (x' + y)
≤cong2 .zero zero y (zero≤ .zero) = isReflexive y
≤cong2 .zero (suc x') zero (zero≤ .(suc x')) = zero≤ (suc (x' + zero))
≤cong2 .zero (suc x') (suc y) (zero≤ .(suc x')) = mono≤ y (x' + suc y) {!   !}
≤cong2 .(suc x) .(suc x') y (mono≤ x x' xx) = mono≤ (x + y) (x' + y) {!   !}        
-}

≤cong2 : (x x₁ y : Nat) → x ≤ x₁ → (x + y) ≤ (x₁ + y)
≤cong2 .zero x₁ y (zero≤ .x₁) = {!   !}
≤cong2 .(suc x) .(suc x₁) y (mono≤ x x₁ xx₁) = mono≤ (x + y) (x₁ + y) (≤cong2 x x₁ y xx₁) 