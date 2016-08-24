module NatAlt where

open import Relation.Binary.PropositionalEquality
open import Function using (id) renaming (_∘′_ to _∘_)
open ≡-Reasoning renaming (_≡⟨⟩_ to _≡[]≡_; _≡⟨_⟩_ to _≡[_]≡_)


-- Definitions: naturals, function iteration, and addition.
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_^_ : {A : Set} → (A → A) → ℕ → (A → A)
f ^ zero = id
f ^ suc n = λ x → (f ^ n) (f x)

_+_ : ℕ → ℕ → ℕ
a + b = ((suc ^ a) ∘ (suc ^ b)) 0


-- Helper lemmas.
^-mono : ∀ {m} {A : Set} → (f : A → A) → f ^ (suc m) ≡ f ∘ (f ^ m)
^-mono {zero} f = refl
^-mono {suc m} f = cong (λ eq → λ x → eq (f x)) (^-mono {m} f)

^-suc : ∀ {m} → m ≡ (suc ^ m) 0
^-suc {zero} = refl
^-suc {suc m} =
  begin
    suc m               ≡[ cong suc (^-suc {m}) ]≡
    suc ((suc ^ m) 0)   ≡[]≡
    (suc ∘ (suc ^ m)) 0 ≡[ cong-app (sym (^-mono {m} suc)) 0 ]≡
    (suc ^ suc m) 0     ∎

+-0 : ∀ {n} → 0 + n ≡ n
+-0 {n} =
  begin
    0 + n              ≡[]≡
    (id ∘ (suc ^ n)) 0 ≡[]≡
    (suc ^ n) 0        ≡[ sym (^-suc {n}) ]≡
    n ∎

+-suc : ∀ {m n} → (suc m) + n ≡ suc (m + n)
+-suc {m} {n} =
  begin
    suc m + n                       ≡[]≡
    ((suc ^ suc m) ∘ (suc ^ n)) 0   ≡[ cong-app (cong₂ _∘_ {u = suc ^ n} (^-mono {m} suc) refl) 0 ]≡
    (suc ∘ (suc ^ m) ∘ (suc ^ n)) 0 ≡[]≡
    suc (((suc ^ m) ∘ (suc ^ n)) 0) ≡[]≡
    suc (m + n) ∎

^-comm₁ : ∀ {m} {A : Set} → (f : A → A) → f ∘ (f ^ m) ≡ (f ^ m) ∘ f
^-comm₁ {zero} f = refl
^-comm₁ {suc m} f =
  begin
    f ∘ (f ^ suc m) ≡[ cong₂ _∘_ {f} refl (^-mono {m} f) ]≡
    f ∘ f ∘ (f ^ m) ≡[ cong₂ _∘_ {f} refl (^-comm₁ {m} f) ]≡
    f ∘ (f ^ m) ∘ f ≡[ cong₂ _∘_ {u = f} (sym (^-mono {m} f)) refl ]≡
    (f ^ suc m) ∘ f ∎

^-comm : ∀ {m n} {A : Set} → (f : A → A) → (f ^ m) ∘ (f ^ n) ≡ (f ^ n) ∘ (f ^ m)
^-comm {zero} f = refl
^-comm {suc m} {n} f =
  begin
    (f ^ suc m) ∘ (f ^ n) ≡[ cong₂ _∘_ (^-mono {m} f) refl ]≡
    f ∘ (f ^ m) ∘ (f ^ n) ≡[ cong₂ _∘_ {f} refl (^-comm {m} {n} f)  ]≡
    f ∘ (f ^ n) ∘ (f ^ m) ≡[ cong₂ _∘_ {u = f ^ m} (^-comm₁ {n} f) refl ]≡
    (f ^ n) ∘ f ∘ (f ^ m) ≡[ cong₂ _∘_ {f ^ n} refl (sym (^-mono {m} f)) ]≡
    (f ^ n) ∘ (f ^ suc m) ∎

^-dist : ∀ {m n} {A : Set} → (f : A → A) → f ^ (m + n) ≡ (f ^ m) ∘ (f ^ n)
^-dist {zero} {n} f = f ^ (0 + n) ≡[ cong₂ _^_ {f} refl (+-0 {n}) ]≡ f ^ n ∎
^-dist {suc m} {n} f =
  begin
    f ^ (suc m + n)       ≡[ cong₂ _^_ {f} refl (+-suc {m} {n}) ]≡
    f ^ (suc (m + n))     ≡[ ^-mono {m + n} f ]≡
    f ∘ (f ^ (m + n))     ≡[ cong₂ _∘_ {f} refl (^-dist {m} {n} f) ]≡
    f ∘ (f ^ m) ∘ (f ^ n) ≡[ cong₂ _∘_ {u = f ^ n} (sym (^-mono {m} f)) refl ]≡
    (f ^ suc m) ∘ (f ^ n) ∎


-- Main theorems: commutativity and associativity of addition on ℕ.
+-comm : ∀ {m n} → m + n ≡ n + m
+-comm {m} {n} =
  begin
    m + n                     ≡[]≡
    ((suc ^ m) ∘ (suc ^ n)) 0 ≡[ cong-app (^-comm {m} {n} suc) 0 ]≡
    ((suc ^ n) ∘ (suc ^ m)) 0 ≡[]≡
    n + m ∎

+-assoc : ∀ {m n o} → m + (n + o) ≡ (m + n) + o
+-assoc {m} {n} {o} =
  begin
    m + (n + o)                           ≡[]≡
    ((suc ^ m) ∘ (suc ^ (n + o))) 0       ≡[ cong-app (cong₂ _∘_ {suc ^ m} refl (^-dist {n} {o} suc)) 0 ]≡
    ((suc ^ m) ∘ (suc ^ n) ∘ (suc ^ o)) 0 ≡[ cong-app (cong₂ _∘_ {u = suc ^ o} (sym (^-dist {m} {n} suc)) refl) 0 ]≡
    ((suc ^ (m + n)) ∘ (suc ^ o)) 0       ≡[]≡
    (m + n) + o ∎
