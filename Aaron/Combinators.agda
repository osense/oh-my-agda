module Combinators where

open import Relation using (_≡_; refl; ∧-elim₁; ∧-elim₂)
open import Nat using (ℕ; suc; _+_; _>_; <-trans; <-mono₂; <-mono₂'; <-suc+; <-suc)
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
Sfree (a ⋅ b) = Sfree a ∧ Sfree b


Sfree-↝-size< : ∀ {a b} → Sfree a ≡ ⊤ → a ↝ b → size a > size b ≡ ⊤
Sfree-↝-size< f (↝K a b) = <-trans {size a} {suc (suc (size a + size b))} {suc (suc (suc (size a + size b)))} (<-trans {size a} {suc (size a + size b)} {suc (suc (size a + size b))} (<-suc+ {size a} {size b}) (<-suc {size a + size b})) (<-suc {size a + size b}) -- lol
Sfree-↝-size< () (↝S a b c)
Sfree-↝-size< f (↝Cong₁ {a} {a'} b p) = <-mono₂ {size a} {size a'} {size b} (Sfree-↝-size< (∧-elim₁ f) p)
Sfree-↝-size< f (↝Cong₂ a {b} {b'} p) = <-mono₂' {size b} {size b'} {size a} (Sfree-↝-size< (∧-elim₂ {Sfree a} {Sfree b} f) p)
