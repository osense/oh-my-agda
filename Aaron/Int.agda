module Int where

import Nat using (_+_; _≤_; ≤-antisym)
open import Nat using (ℕ; zero; suc)
open import Bool using (𝔹; ⊤; ⊥; ¬_; _⇒_; _⊕_; if_then_else)
open import Relation using (_≡_; refl; Unit; U; cong₂; 𝔹-contra; antisym)


ℤ-s : ℕ → Set
ℤ-s zero = Unit
ℤ-s (suc n) = 𝔹

data ℤ : Set where
  _±_ : (n : ℕ) → ℤ-s n → ℤ
infixl 10 _±_


diff : ℕ → ℕ → ℤ
diff zero zero = zero ± U
diff zero (suc b) = suc b ± ⊥
diff (suc a) zero = suc a ± ⊤
diff (suc a) (suc b) = diff a b

_+_ : ℤ → ℤ → ℤ
(zero ± U) + b = b
a + (zero ± U) = a
(suc a ± s) + (suc b ± s') with s ⊕ s'
(suc a ± s) + (suc b ± s') | ⊤ = if s then diff (suc a) (suc b) else (diff (suc b) (suc a))
(suc a ± s) + (suc b ± s') | ⊥ = ((suc a) Nat.+ (suc b)) ± s

_≤_ : ℤ → ℤ → 𝔹
(zero ± U) ≤ (zero ± U) = ⊤
(zero ± U) ≤ (suc n ± s') = s'
(suc a ± s) ≤ (zero ± U) = ¬ s
(suc a ± s) ≤ (suc b ± s') with s ⊕ s'
(suc a ± s) ≤ (suc b ± s') | ⊤ = s' ⇒ s
(suc a ± s) ≤ (suc b ± s') | ⊥ = if s then (a Nat.≤ b) else (b Nat.≤ a)

≤-antisym : antisym _≤_
≤-antisym {zero ± U} {zero ± U} p₁ p₂ = refl
≤-antisym {zero ± U} {suc b ± s'} p₁ p₂ rewrite p₁ = 𝔹-contra p₂
≤-antisym {suc a ± s} {zero ± U} p₁ p₂ rewrite p₂ = 𝔹-contra p₁
≤-antisym {suc a ± s} {suc b ± s'} p₁ p₂ with s | s'
≤-antisym {suc a ± s} {suc b ± s'} p₁ p₂ | ⊤ | ⊤ rewrite Nat.≤-antisym {a} {b} p₁ p₂ = refl
≤-antisym {suc a ± s} {suc b ± s'} p₁ p₂ | ⊤ | ⊥ = 𝔹-contra p₂
≤-antisym {suc a ± s} {suc b ± s'} p₁ p₂ | ⊥ | ⊤ = 𝔹-contra p₁
≤-antisym {suc a ± s} {suc b ± s'} p₁ p₂ | ⊥ | ⊥ rewrite Nat.≤-antisym {a} {b} p₂ p₁ = refl

