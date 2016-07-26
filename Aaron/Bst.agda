open import Relation using (_≡_; refl; inspect; _with≡_; reflexive; antisym; transitive; total)
open import Bool
open import Product

module Bst (A : Set) (_≤A_ : A → A → 𝔹)
           (≤-refl : reflexive _≤A_)
           (≤-antisym : antisym _≤A_)
           (≤-trans : transitive _≤A_)
           (≤-total : total _≤A_) where

open import MinMax (A) (_≤A_) (≤-refl) (≤-trans) (≤-total)


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


dec-lb : {l l' u : A} → Bst l u → l' ≤A l ≡ ⊤ → Bst l' u
dec-lb (leaf p') p = leaf (≤-trans p p')
dec-lb (node d l r p₁ p₂) p = node d l r (≤-trans p p₁) p₂

inc-ub : {l u u' : A} → Bst l u → u ≤A u' ≡ ⊤ → Bst l u'
inc-ub (leaf p') p = leaf (≤-trans p' p)
inc-ub (node d l r p₁ p₂) p = node d l r p₁ (≤-trans p₂ p)


insert : ∀ {l u} → (d : A) → Bst l u → Bst (min d l) (max d u)
insert d (leaf p) = node d (leaf ≤-refl) (leaf ≤-refl) min-≤1 max-≤1
insert d (node d' L R p₁ p₂) with inspect (d ≤A d')
insert d (node d' L R p₁ p₂) | ⊤ with≡ p with insert d L
insert d (node d' L R p₁ p₂) | ⊤ with≡ p | L' rewrite p = node d' L' (inc-ub R (≤-trans p₂ max-≤2)) (min-mono p₁) ≤-refl
insert d (node d' L R p₁ p₂) | ⊥ with≡ p with insert d R
insert d (node d' L R p₁ p₂) | ⊥ with≡ p | R' rewrite p = node d' (dec-lb L p₁) R' min-≤2 (max-mono p₂)
