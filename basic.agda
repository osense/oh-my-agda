module basic where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + b = b
(succ a) + b = succ (a + b)

_*_ : ℕ → ℕ → ℕ
zero * b = zero
(succ a) * b = b + (a * b)


data _×_ (A B : Set) : Set where
  _,_ : A → B → (A × B)


data Fin : ℕ → Set where
  zero' : {n : ℕ} → Fin (succ n)
  succ' : {n : ℕ} → Fin n → Fin (succ n)

fin : ∀ (n : ℕ) → Fin (succ n)
fin zero = zero'
fin (succ n) = succ' (fin n)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

flip : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
flip f = λ a b → f b a
