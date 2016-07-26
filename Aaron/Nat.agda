module Nat where

open import Bool
open import Relation using (_≡_; refl; 𝔹-contra; antisym)


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
infixl 8 _+_

suc-inj : ∀ {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

+0 : ∀ (x : ℕ) → x + zero ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + suc y ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl


_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n
infixl 9 _*_

*distrib : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distrib zero y z = refl
*distrib (suc x) y z rewrite *distrib x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*suc : ∀ (x y : ℕ) →  x * suc y ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y | +assoc x y (x * y) | +comm x y | +assoc y x (x * y) = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*assoc zero y z = refl
*assoc (suc x) y z rewrite *distrib y (x * y) z | *assoc x y z = refl


_<_ : ℕ → ℕ → 𝔹
zero < zero = ⊥
zero < suc y = ⊤
suc x < zero = ⊥
suc x < suc y = x < y

<-0 : ∀ (x : ℕ) → x < 0 ≡ ⊥
<-0 zero = refl
<-0 (suc x) = refl

<-trans : ∀ {x y z : ℕ} → x < y ≡ ⊤ → y < z ≡ ⊤ → x < z ≡ ⊤
<-trans {x} {0} p₁ p₂ rewrite <-0 x = 𝔹-contra p₁
<-trans {0} {suc y} {0} p₁ ()
<-trans {0} {suc y} {suc z} p₁ p₂ = refl
<-trans {suc x} {suc y} {0} p₁ ()
<-trans {suc x} {suc y} {suc z} p₁ p₂ = <-trans {x} {y} {z} p₁ p₂


_=ℕ_ : ℕ → ℕ → 𝔹
0 =ℕ 0 = ⊤
suc x =ℕ suc y = x =ℕ y
_ =ℕ _ = ⊥

_≤_ : ℕ → ℕ → 𝔹
x ≤ y = (x < y) ∨ (x =ℕ y)

≤-suc : ∀ x → x ≤ suc x ≡ ⊤
≤-suc zero = refl
≤-suc (suc x) = ≤-suc x

≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ ⊤ → y ≤ z ≡ ⊤ → x ≤ z ≡ ⊤
≤-trans {zero} {z = zero} p₁ p₂ = refl
≤-trans {zero} {z = suc z} p₁ p₂ = refl
≤-trans {suc x} {zero} ()
≤-trans {suc x} {suc y} {zero} p₁ ()
≤-trans {suc x} {suc y} {suc z} = ≤-trans {x} {y} {z}

≤-total : ∀ {x y : ℕ} → x ≤ y ≡ ⊥ → y ≤ x ≡ ⊤
≤-total {zero} {zero} p = refl
≤-total {zero} {suc y} ()
≤-total {suc x} {zero} p = refl
≤-total {suc x} {suc y} p rewrite ≤-total {x} {y} p = refl

≤-antisym : antisym _≤_
≤-antisym {zero} {zero} p₁ p₂ = refl
≤-antisym {zero} {suc b} p₁ ()
≤-antisym {suc a} {zero} ()
≤-antisym {suc a} {suc b} p₁ p₂ rewrite ≤-antisym {a} {b} p₁ p₂ = refl

=ℕ-refl : ∀ (x : ℕ) → x =ℕ x ≡ ⊤
=ℕ-refl zero = refl
=ℕ-refl (suc x) = =ℕ-refl x

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ ⊤ → x ≡ y
=ℕ-to-≡ {0} {0} p = refl
=ℕ-to-≡ {0} {suc y} ()
=ℕ-to-≡ {suc x} {0} ()
=ℕ-to-≡ {suc x} {suc y} p rewrite =ℕ-to-≡ {x} {y} p = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ ⊤
=ℕ-from-≡ {x} refl = =ℕ-refl x
