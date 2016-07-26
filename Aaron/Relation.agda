module Relation where

open import Agda.Primitive using (_⊔_)
open import Bool using (𝔹; ⊤; ⊥; _∧_; if_then_else)


data _≡_ {l} {A : Set l} (x : A) : A → Set l where
  refl : x ≡ x
infixr 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}


sym : ∀ {l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
sym p rewrite p = refl

cong₂ : ∀ {l} {A B C : Set l} {a₁ a₂ : A} {b₁ b₂ : B}
        → (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ f p₁ p₂ rewrite p₁ | p₂ = refl


𝔹-contra : ⊥ ≡ ⊤ → ∀ {P : Set} → P
𝔹-contra ()


data Singleton {l} {A : Set l} (x : A) : Set l where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {l} {A : Set l} (x : A) → Singleton x
inspect x = x with≡ refl


reflexive : ∀ {l} {A : Set l} → (_≥A_ : A → A → 𝔹) → Set l
reflexive _≥_ = ∀ {a} → a ≥ a ≡ ⊤

antisym : ∀ {l} {A : Set l} → (_≥A_ : A → A → 𝔹) → Set l
antisym _≥_ = ∀ {a b} → a ≥ b ≡ ⊤ → b ≥ a ≡ ⊤ → a ≡ b 

transitive : ∀ {l} {A : Set l} → (_≥A_ : A → A → 𝔹) → Set l
transitive _≥_ = ∀ {a b c} → a ≥ b ≡ ⊤ → b ≥ c ≡ ⊤ → a ≥ c ≡ ⊤

total : ∀ {l} {A : Set l} → (_≥A_ : A → A → 𝔹) → Set l
total _≥_ = ∀ {a b} → a ≥ b ≡ ⊥ → b ≥ a ≡ ⊤


total-reflexive : ∀ {l} {A : Set l} → (_≥A_ : A → A → 𝔹) → total _≥A_ → reflexive _≥A_
total-reflexive _≥_ tot {a} with inspect (a ≥ a)
total-reflexive _≥_ tot {a} | ⊤ with≡ p = p
total-reflexive _≥_ tot {a} | ⊥ with≡ p = tot p

