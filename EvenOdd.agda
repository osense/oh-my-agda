module EvenOdd where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Solver
open import Data.Product

open +-*-Solver


Even : ℕ → Set
Even n = ∃[ m ] (n ≡ 2 * m)

Odd : ℕ → Set
Odd n = ∃[ m ] (n ≡ 2 * m + 1)

even-suc : ∀ {n} → Even n → Odd (n + 1)
even-suc (n/2 , refl) = n/2 , refl

_ : 1 + 1 ≡ 2
_ = solve 0 (con 1 :+ con 1 , (con 2)) refl

_ : ∀ n → n + n ≡ 2 * n
_ = λ n → solve 1 (λ x → (x :+ x) , (con 2 :* x)) refl n

-- Goal: n/2 + (n/2 + zero) + 1 + 1 ≡ n/2 + 1 + (n/2 + 1 + zero)
odd-suc : ∀ {n} → Odd n → Even (n + 1)
odd-suc (n/2 , refl) = (n/2 + 1) , solve 1 rep refl n/2
  where
    lhs = λ n/2 → n/2 :+ (n/2 :+ (con 0)) :+ con 1 :+ con 1
    rhs = λ n/2 → n/2 :+ con 1 :+ (n/2 :+ con 1 :+ con 0)
    rep = λ n/2 → lhs n/2 , rhs n/2

-- Goal: m/2 + (m/2 + zero) + (n/2 + (n/2 + zero)) ≡ m/2 + n/2 + (m/2 + n/2 + zero)
even+even : ∀ {m n} → Even m → Even n → Even (m + n)
even+even (m/2 , refl) (n/2 , refl) = (m/2 + n/2) , solve 2 rep refl m/2 n/2
  where
    rep =
      λ m/2 n/2 →
        let lhs = m/2 :+ (m/2 :+ con 0) :+ (n/2 :+ (n/2 :+ con 0))
            rhs = m/2 :+ n/2 :+ (m/2 :+ n/2 :+ con 0)
        in lhs , rhs

-- Goal: [m-1]/2 + ([m-1]/2 + zero) + 1 + ([n-1]/2 + ([n-1]/2 + zero) + 1)
--     ≡ [m-1]/2 + [n-1]/2 + 1 + ([m-1]/2 + [n-1]/2 + 1 + zero)
odd+odd : ∀ {m n} → Odd m → Odd n → Even (m + n)
odd+odd ([m-1]/2 , refl) ([n-1]/2 , refl) = [m+n]/2 , solve 2 rep refl [m-1]/2 [n-1]/2
  where
    [m+n]/2 = [m-1]/2 + [n-1]/2 + 1
    rep =
      λ a b →
        let lhs = a :+ (a :+ con 0) :+ con 1 :+ (b :+ (b :+ con 0) :+ con 1)
            rhs = a :+ b :+ con 1 :+ (a :+ b :+ con 1 :+ con 0)
        in lhs , rhs

-- Goal: m/2 + (m/2 + zero) + ([n-1]/2 + ([n-1]/2 + zero) + 1)
--     ≡ m/2 + [n-1]/2 + (m/2 + [n-1]/2 + zero) + 1
even+odd : ∀ {m n} → Even m → Odd n → Odd (m + n)
even+odd (m/2 , refl) ([n-1]/2 , refl) = (m/2 + [n-1]/2) , solve 2 rep refl m/2 [n-1]/2
  where
    rep =
      λ a b →
        let lhs = a :+ (a :+ con 0) :+ (b :+ (b :+ con 0) :+ con 1)
            rhs = a :+ b :+ (a :+ b :+ con 0) :+ con 1
        in lhs , rhs

-- Goal: (m/2 + (m/2 + zero)) * n ≡ m/2 * n + (m/2 * n + zero)
even*n : ∀ {m} → Even m → (n : ℕ) → Even (m * n)
even*n (m/2 , refl) n = m/2 * n , solve 2 rep refl m/2 n
  where
    rep =
      λ a b →
        let lhs = (a :+ (a :+ con 0)) :* b
            rhs = a :* b :+ (a :* b :+ con 0)
        in lhs , rhs


-- This is nice, but it was more painful than I expected.
