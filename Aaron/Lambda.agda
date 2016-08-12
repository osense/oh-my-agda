module Lambda where

open import String
open import Bool using (𝔹; ⊤; ⊥; _∨_; if_then_else)
open import Relation using (_≡_; refl; inspect; _with≡_; Tc; step; trans)


data Comb : Set where
  S K : Comb
  var : String → Comb
  _⋅_ : Comb → Comb → Comb
infixl 10 _⋅_


λ* : String → Comb → Comb
λ* s S = K ⋅ S
λ* s K = K ⋅ K
λ* s (var s') = if s == s' then S ⋅ K ⋅ K else (K ⋅ (var s'))
λ* s (c₁ ⋅ c₂) = S ⋅ (λ* s c₁) ⋅ (λ* s c₂)

contains-var : String → Comb → 𝔹
contains-var s S = ⊥
contains-var s K = ⊥
contains-var s (var s') = s == s'
contains-var s (c₁ ⋅ c₂) = contains-var s c₁ ∨ contains-var s c₂

λ*-binds : ∀ s c → contains-var s (λ* s c) ≡ ⊥
λ*-binds s S = refl
λ*-binds s K = refl
λ*-binds s (var s') with inspect (s == s')
λ*-binds s (var s') | ⊤ with≡ p rewrite p = refl
λ*-binds s (var s') | ⊥ with≡ p rewrite p = p
λ*-binds s (c₁ ⋅ c₂) rewrite λ*-binds s c₁ | λ*-binds s c₂ = refl

subst : Comb → String → Comb → Comb
subst e s S = S
subst e s K = K
subst e s (var s') = if s == s' then e else (var s')
subst e s (c₁ ⋅ c₂) = (subst e s c₁) ⋅ (subst e s c₂)


data _↝_ : Comb → Comb → Set where
  ↝K : ∀ {a b} → K ⋅ a ⋅ b ↝ a
  ↝S : ∀ {a b c} → S ⋅ a ⋅ b ⋅ c ↝ (a ⋅ c) ⋅ (b ⋅ c)
  ↝Cong₁ : ∀ {a a' b} → a ↝ a' → a ⋅ b ↝ a' ⋅ b
  ↝Cong₂ : ∀ {a b b'} → b ↝ b' → a ⋅ b ↝ a ⋅ b'
infixr 6 _↝_

_↝⁺_ : Comb → Comb → Set
_↝⁺_ = Tc {_>A_ = _↝_}


trans-Cong₁ : ∀ {a a'} b → a ↝⁺ a' → (a ⋅ b) ↝⁺ (a' ⋅ b)
trans-Cong₁ b (step r) = step (↝Cong₁ r)
trans-Cong₁ b (trans r₁ r₂) = trans (trans-Cong₁ b r₁) (trans-Cong₁ b r₂)

trans-Cong₂ : ∀ a {b b'} → b ↝⁺ b' → (a ⋅ b) ↝⁺ (a ⋅ b')
trans-Cong₂ a (step r) = step (↝Cong₂ r)
trans-Cong₂ a (trans r₁ r₂) = trans (trans-Cong₂ a r₁) (trans-Cong₂ a r₂)

λ*-↝ : ∀ a b s → ((λ* s a) ⋅ b) ↝⁺ (subst b s a)
λ*-↝ S b s = step ↝K
λ*-↝ K b s = step ↝K
λ*-↝ (var s') b s with (s == s')
λ*-↝ (var s') b s | ⊤ = trans (step ↝S) (step ↝K)
λ*-↝ (var s') b s | ⊥ = step ↝K
λ*-↝ (c₁ ⋅ c₂) b s = trans
                       (step ↝S)
                       (trans
                         (trans-Cong₁ ((λ* s c₂) ⋅ b) (λ*-↝ c₁ b s))
                         (trans-Cong₂ (subst b s c₁) (λ*-↝ c₂ b s) ))
