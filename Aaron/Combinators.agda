module Combinators where

open import Nat using (ℕ; suc; _+_)
open import Bool using (𝔹; ⊤; ⊥; _∧_)

data Comb : Set where
  S K : Comb
  _⋅_  : Comb → Comb → Comb
infixl 10 _⋅_

data _↝_ : Comb → Comb → Set where
  ↝K     : (a b : Comb) → (K ⋅ a ⋅ b) ↝ a
  ↝S     : (a b c : Comb) → (S ⋅ a ⋅ b ⋅ c) ↝ (a ⋅ c) ⋅ (b ⋅ c)
  ↝Cong₁ : {a a' : Comb} → (b : Comb) → a ↝ a' → (a ⋅ b) ↝ (a' ⋅ b)
  ↝Cong₂ : (a : Comb) → {b b' : Comb} → b ↝ b' → (a ⋅ b) ↝ (a ⋅ b')
infixl 5 _↝_


size : Comb → ℕ
size S = 1
size K = 1
size (a ⋅ b) = suc (size a + size b)

Sfree : Comb → 𝔹
Sfree S = ⊥
Sfree K = ⊤
Sfree (c₁ ⋅ c₂) = Sfree c₁ ∧ Sfree c₂
