open import Relation using (_≡_; inspect; _with≡_; reflexive; transitive; total)
open import Bool

module MinMax (A : Set) (_≤A_ : A → A → 𝔹)
              (≤-refl : reflexive _≤A_)
              (≤-trans : transitive _≤A_)
              (≤-total : total _≤A_) where


min : A → A → A
min a b = if a ≤A b then a else b

max : A → A → A
max a b = if a ≤A b then b else a

min-≤1 : ∀ {x y} → min x y ≤A x ≡ ⊤
min-≤1 {x} {y} with inspect (x ≤A y)
min-≤1 {x} {y} | ⊤ with≡ p rewrite p = ≤-refl
min-≤1 {x} {y} | ⊥ with≡ p rewrite p = ≤-total p

min-≤2 : ∀ {x y} → min x y ≤A y ≡ ⊤
min-≤2 {x} {y} with inspect (x ≤A y)
min-≤2 {x} {y} | ⊤ with≡ p rewrite p = p
min-≤2 {x} {y} | ⊥ with≡ p rewrite p = ≤-refl

max-≤1 : ∀ {x y} → x ≤A max x y ≡ ⊤
max-≤1 {x} {y} with inspect (x ≤A y)
max-≤1 {x} {y} | ⊤ with≡ p rewrite p = p
max-≤1 {x} {y} | ⊥ with≡ p rewrite p = ≤-refl

max-≤2 : ∀ {x y} → y ≤A max x y ≡ ⊤
max-≤2 {x} {y} with inspect (x ≤A y)
max-≤2 {x} {y} | ⊤ with≡ p rewrite p = ≤-refl
max-≤2 {x} {y} | ⊥ with≡ p rewrite p = ≤-total p

min-mono : ∀ {x y y'} → y ≤A y' ≡ ⊤ → (min x y ≤A min x y') ≡ ⊤
min-mono {x} {y} {y'} p with inspect (x ≤A y) | inspect (x ≤A y')
min-mono {x} {y} {y'} p | ⊤ with≡ p₁ | ⊤ with≡ p₂ rewrite p₁ | p₂ = ≤-refl
min-mono {x} {y} {y'} p | ⊤ with≡ p₁ | ⊥ with≡ p₂ rewrite p₁ | p₂ = ≤-trans p₁ p
min-mono {x} {y} {y'} p | ⊥ with≡ p₁ | ⊤ with≡ p₂ rewrite p₁ | p₂ = ≤-total p₁
min-mono {x} {y} {y'} p | ⊥ with≡ p₁ | ⊥ with≡ p₂ rewrite p₁ | p₂ = p

max-mono : ∀ {x y y'} → y ≤A y' ≡ ⊤ → (max x y ≤A max x y') ≡ ⊤
max-mono {x} {y} {y'} p with inspect (x ≤A y) | inspect (x ≤A y')
max-mono {x} {y} {y'} p | ⊤ with≡ p₁ | ⊤ with≡ p₂ rewrite p₁ | p₂ = p
max-mono {x} {y} {y'} p | ⊤ with≡ p₁ | ⊥ with≡ p₂ rewrite p₁ | p₂ = ≤-trans p (≤-total p₂)
max-mono {x} {y} {y'} p | ⊥ with≡ p₁ | ⊤ with≡ p₂ rewrite p₁ | p₂ = p₂
max-mono {x} {y} {y'} p | ⊥ with≡ p₁ | ⊥ with≡ p₂ rewrite p₁ | p₂ = ≤-refl
