module Combinators where
open import Data.Nat.Base

data Mu (A : Set) : Set where
  roll : A → Mu A

unroll : ∀ {A : Set} → Mu A → A
unroll (roll a) = a

Y : ∀ {A : Set} → (A → A) → A
Y = λ f → (λ x → f (unroll x x)) (roll (λ x → f (unroll x x)))


fac : (ℕ → ℕ) → ℕ → ℕ
fac f zero = suc zero
fac f n = n * f (pred n)
