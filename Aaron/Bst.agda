open import Relation using (_≡_; refl; inspect; _with≡_; antisym)
open import Bool
open import Product

module Bst (A : Set) (_≤A_ : A → A → 𝔹)
           (≤-antisym : antisym _≤A_) where


data Bst : A → A → Set where
  leaf : {l u : A} → l ≤A u ≡ ⊤ → Bst l u
  node : {l l' u' u : A} → (d : A) → Bst l' d → Bst d u' →
         l ≤A l' ≡ ⊤ → u' ≤A u ≡ ⊤ →
         Bst l u


search : ∀ {l u} → (d : A) → Bst l u → Maybe (Σ A (λ d' → d ≡ d'))
search d (leaf _) = nothing
search d (node d' l r _ _) with inspect (d ≤A d')
search d (node d' l r _ _) | ⊤ with≡ p₁ with inspect (d' ≤A d)
search d (node d' l r _ _) | ⊤ with≡ p₁ | ⊤ with≡ p₂ = just (d' , ≤-antisym p₁ p₂)
search d (node d' l r _ _) | ⊤ with≡ p₁ | ⊥ with≡ p₂ = search d l
search d (node d' l r _ _) | ⊥ with≡ p₁ = search d r
