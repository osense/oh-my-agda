{-# OPTIONS --without-K --safe #-}

module EvenOdd where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product

--open import Data.Nat.Solver
open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.AlmostCommutativeRing.Instances
open import Polynomial.Simple.Reflection
--open +-*-Solver

--open AlmostCommutativeRing Nat.ring


Even : ℕ → Set
Even n = ∃[ m ] (n ≡ 2 * m)

Odd : ℕ → Set
Odd n = ∃[ m ] (n ≡ 2 * m + 1)

_ : Even 2
_ = 1 , refl

_ : Odd 5
_ = 2 , refl

[_-1] : ∀ {n} → Odd n → ℕ
[_-1] {zero} (zero , ())
[_-1] {suc n} _ = n
infix 10 [_-1]

-- The proofs of (Even n) and (Odd (n + 1)) are the same.
even-suc : ∀ {n} → Even n → Odd (n + 1)
even-suc (n/2 , refl) = n/2 , refl

_ : 1 + 1 ≡ 2
_ = solve Nat.ring

_ : ∀ n → n + n ≡ 2 * n
_ = solve Nat.ring

odd-suc : ∀ {n} → Odd n → Even (n + 1)
odd-suc (n/2 , refl) = (n/2 + 1) , lemma n/2
  where
    lemma : ∀ n/2 → n/2 + (n/2 + zero) + 1 + 1 ≡ n/2 + 1 + (n/2 + 1 + zero)
    lemma = solve Nat.ring

even+even : ∀ {m n} → Even m → Even n → Even (m + n)
even+even (m/2 , refl) (n/2 , refl) = (m/2 + n/2) , lemma m/2 n/2
  where
    lemma : ∀ m/2 n/2 → m/2 + (m/2 + zero) + (n/2 + (n/2 + zero)) ≡
                  m/2 + n/2 + (m/2 + n/2 + zero)
    lemma = solve Nat.ring

odd+odd : ∀ {m n} → Odd m → Odd n → Even (m + n)
odd+odd ([m-1]/2 , refl) ([n-1]/2 , refl) = [m+n]/2 , lemma [m-1]/2 [n-1]/2
  where
    lemma : ∀ [m-1]/2 [n-1]/2 → [m-1]/2 + ([m-1]/2 + zero) + 1 + ([n-1]/2 + ([n-1]/2 + zero) + 1) ≡
                                    [m-1]/2 + [n-1]/2 + 1 + ([m-1]/2 + [n-1]/2 + 1 + zero)
    lemma = solve Nat.ring
    [m+n]/2 = [m-1]/2 + [n-1]/2 + 1

even+odd : ∀ {m n} → Even m → Odd n → Odd (m + n)
even+odd (m/2 , refl) ([n-1]/2 , refl) = (m/2 + [n-1]/2) , lemma m/2 [n-1]/2
  where
    lemma : ∀ m/2 [n-1]/2 → m/2 + (m/2 + zero) + ([n-1]/2 + ([n-1]/2 + zero) + 1) ≡
                                m/2 + [n-1]/2 + (m/2 + [n-1]/2 + zero) + 1
    lemma = solve Nat.ring

even*n : ∀ {m} → Even m → (n : ℕ) → Even (m * n)
even*n (m/2 , refl) n = m/2 * n , lemma m/2 n
  where
    lemma : ∀ m/2 n → (m/2 + (m/2 + zero)) * n ≡ m/2 * n + (m/2 * n + zero)
    lemma = solve Nat.ring

-- Is this right?
odd*odd : ∀ {m n} → Odd m → Odd n → Odd (m * n)
odd*odd {m} {n} ([m-1]/2 , refl) no@([n-1]/2 , refl) = ([m-1]/2 * [n-1]/2 + m + [ no -1]) , lemma
  where
    lemma : {!!}
    lemma = {!!}
