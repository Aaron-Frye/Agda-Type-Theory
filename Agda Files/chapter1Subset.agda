open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- if_then_else_ : ∀ {A : Set} → Bool → A → A → A 
-- if true  then x else y = x 
-- if false then x else y = y

data Types : Set where
    ℕ : Types
    𝔹 : Types

data Terms : Set where
    nVal : Nat → Terms
    bVal : Bool → Terms
    Add : Terms → Terms → Terms
    If : Terms → Terms → Terms → Terms
    Lt : Terms → Terms → Terms

data _⟶_ : Terms → Terms → Set where
    plus : (n₁ n₂ : Nat) → (Add (nVal n₁) (nVal n₂) ⟶ (nVal (n₁ + n₂)))
    cmp : (n₁ n₂ : Nat) → (Lt (nVal n₁) (nVal n₂)) ⟶ (bVal (n₁ < n₂))
    if1 : (p₁ p₂ : Terms) → (If (bVal true) p₁ p₂) ⟶ p₁
    if2 : (p₁ p₂ : Terms) → (If (bVal false) p₁ p₂) ⟶ p₂
    pluscong1 : (p₁ p₁' p₂ : Terms) → (p₁ ⟶ p₁') → (Add p₁ p₂) ⟶ (Add p₁' p₂)
    pluscong2 : (p₁ p₂ p₂' : Terms) → (p₂ ⟶ p₂') → (Add p₁ p₂) ⟶ (Add p₁ p₂')
    ltcong1 : (p₁ p₁' p₂ : Terms) → (p₁ ⟶ p₁') → (Lt p₁ p₂) ⟶ (Lt p₁' p₂)
    ltcong2 : (p₁ p₂ p₂' : Terms) → (p₂ ⟶ p₂') → (Lt p₁ p₂) ⟶ (Lt p₁ p₂')
    ifcong : (p p' p₁ p₂ : Terms) → (p ⟶ p') → (If p p₁ p₂) ⟶ (If p' p₁ p₂)

test : Nat 
test = {! if_then_else_ true 0 1  !}

data ⊢_⦂_ : Terms → Types → Set where
    bConst : (b : Bool) → ⊢ (bVal b) ⦂ 𝔹
    nConst : (n : Nat) → ⊢ (nVal n) ⦂ ℕ
    typePlus : (p₁ p₂ : Terms) → ⊢ p₁ ⦂ ℕ → ⊢ p₂ ⦂ ℕ → ⊢ (Add p₁ p₂) ⦂ ℕ
    typeLt : (p₁ p₂ : Terms) → ⊢ p₁ ⦂ ℕ → ⊢ p₂ ⦂ ℕ → ⊢ (Lt p₁ p₂) ⦂ 𝔹
    typeIf : (A : Types) → (p p₁ p₂ : Terms) → ⊢ p ⦂ 𝔹 → ⊢ p₁ ⦂ A → ⊢ p₂ ⦂ A → ⊢ (If p p₁ p₂) ⦂ A

subred : ∀ (p : Terms) → (A : Types) → (⊢ p ⦂ A) → (p' : Terms) → (p ⟶ p') → (⊢ p' ⦂ A)
subred .(Add (nVal n₁) (nVal n₂)) .ℕ (typePlus .(nVal n₁) .(nVal n₂) p⦂A p⦂A₁) .(nVal (n₁ + n₂)) (plus n₁ n₂) = nConst (n₁ + n₂)
subred .(Add p₁ p₂) .ℕ (typePlus p₁ p₂ p⦂A p⦂A₁) .(Add p₁' p₂) (pluscong1 .p₁ p₁' .p₂ pp') = typePlus p₁' p₂ (subred p₁ ℕ p⦂A p₁' pp') p⦂A₁
subred .(Add p₁ p₂) .ℕ (typePlus p₁ p₂ p⦂A p⦂A₁) .(Add p₁ p₂') (pluscong2 .p₁ .p₂ p₂' pp') = {!   !}
subred .(Lt p₁ p₂) .𝔹 (typeLt p₁ p₂ p⦂A p⦂A₁) p' pp' = {!   !}
subred .(If p p₁ p₂) A (typeIf .A p p₁ p₂ p⦂A p⦂A₁ p⦂A₂) p' pp' = {!   !}