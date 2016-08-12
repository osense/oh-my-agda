module Combinators where

open import Relation using (_≡_; refl; ∧-intro; ∧-elim₁; ∧-elim₂)
open import Nat using (ℕ; suc; _+_; _>_; <-trans; <-mono₂; <-mono₂'; <-suc+; <-suc)
open import Bool using (𝔹; ⊤; ⊥; _∧_)
open import Product using (Σ; _,_)
open import Termination


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

↝-preserves-Sfree : ∀ {a b} → Sfree a ≡ ⊤ → a ↝ b → Sfree b ≡ ⊤
↝-preserves-Sfree f (↝K a b) = ∧-elim₁ f
↝-preserves-Sfree () (↝S a b c)
↝-preserves-Sfree f (↝Cong₁ {a} b c) = ∧-intro (↝-preserves-Sfree (∧-elim₁ f) c) (∧-elim₂ {Sfree a} f)
↝-preserves-Sfree f (↝Cong₂ a c) = ∧-intro (∧-elim₁ {Sfree a} f) (↝-preserves-Sfree (∧-elim₂ {Sfree a} f) c)


Sfree-comb : Set
Sfree-comb = Σ Comb (λ c → Sfree c ≡ ⊤)

_↝Sfree_ : Sfree-comb → Sfree-comb → Set
(a , _) ↝Sfree (b , _) = a ↝ b

Sfree-size : Sfree-comb → ℕ
Sfree-size (a , _) = size a

Sfree-comb-↝-size< : ∀ {a b} → a ↝Sfree b → (Sfree-size a) > (Sfree-size b) ≡ ⊤
Sfree-comb-↝-size< {a , p₁} {b , _} p = Sfree-↝-size< p₁ p


open measure {A = Sfree-comb}
             _↝Sfree_
             (λ x y → x > y ≡ ⊤)
             Sfree-size
             (λ {a} {b} → Sfree-comb-↝-size< {a} {b})

Sfree-terminates-h : ∀ {a} {p : Sfree a ≡ ⊤} → ↓ _↝Sfree_ (a , p) → ↓ _↝_ a
Sfree-terminates-h {a} {p} (pf↓ x) = pf↓ h
  where h : ∀ {b} → a ↝ b → ↓ _↝_ b
        h {b} u = Sfree-terminates-h (x {b , ↝-preserves-Sfree p u} u)

measure-decrease : ∀ a → ↓ _↝Sfree_ a
measure-decrease a = measure-↓ (↓-> (Sfree-size a))

Sfree-terminates : ∀ a → Sfree a ≡ ⊤ → ↓ _↝_ a
Sfree-terminates a p = Sfree-terminates-h (measure-decrease (a , p))

