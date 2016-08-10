module Relation where

open import Agda.Primitive using (_⊔_)
open import Bool using (𝔹; ⊤; ⊥; _∧_; if_then_else)


data _≡_ {l} {A : Set l} (x : A) : A → Set l where
  refl : x ≡ x
infixr 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data Unit : Set where
  U : Unit

data Empty : Set where

Empty-elim : ∀ {l} {P : Set l} → Empty → P
Empty-elim ()

¬_ : ∀ {l} → Set l → Set l
¬ P = P → Empty

Empty-contra : ∀ {l} {P Q : Set l} → P → ¬ P → Q
Empty-contra p np = Empty-elim (np p)

𝔹-contra : ⊥ ≡ ⊤ → ∀ {P : Set} → P
𝔹-contra ()

_≢_ : ∀ {l} {A : Set l} → A → A → Set l
A ≢ B = ¬(A ≡ B)


∧-elim₁ : ∀ {A B} → A ∧ B ≡ ⊤ → A ≡ ⊤
∧-elim₁ {⊤} p = refl
∧-elim₁ {⊥} ()

∧-elim₂ : ∀ {A B} → A ∧ B ≡ ⊤ → B ≡ ⊤
∧-elim₂ {⊤} p = p
∧-elim₂ {⊥} ()


sym : ∀ {l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

cong : ∀ {l} {A B : Set l} {a a' : A} → (f : A → B) → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong₂ : ∀ {l} {A B C : Set l} {a₁ a₂ : A} {b₁ b₂ : B}
        → (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ f refl refl = refl


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

