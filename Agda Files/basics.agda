data Nat : Set where
    zero : Nat
    suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = suc (x + y)

data Bool : Set where
    true  : Bool
    false : Bool

not : Bool → Bool
not true = false
not false = true

id : (A : Set) → A → A
id A x = x

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A
infixr 5 _::_

data _×_ (A B : Set) : Set where
    _,_ : A → B -> A × B 
infixr 4 _,_

length : {A : Set} → List A → Nat
length [] = 0
length (x :: y) = 1 + (length y)

data Vec (A : Set) : Nat → Set where
    [] :  Vec A 0
    _::Vec_ : {n : Nat} → A → Vec A n -> Vec A (suc n)

infixr 5 _::Vec_

zeroes : (n : Nat) → Vec Nat n
zeroes zero = []
zeroes (suc n) = 0 ::Vec zeroes n

downfrom : (n : Nat) → Vec Nat n
downfrom zero = []
downfrom (suc n) = n ::Vec downfrom n

Eq : Set → Set
Eq A = A → A → Bool

Eqlemma : (A : Set) → Eq A → Eq (Nat -> A)
Eqlemma A f = λ x y → f (x 3) (y 2)