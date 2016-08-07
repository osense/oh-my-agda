module Termination where

open import Agda.Primitive
open import Relation using (_≡_)
open import Bool using (𝔹; ⊤; ⊥)
open import Nat using (ℕ; suc; _>_; <-drop)
open import Product


data ↓ {l l'} {A : Set l} (_>_ : A → A → Set l') : A → Set (l ⊔ l') where
  pf↓ : ∀ {x} → (∀ {y} → x > y → ↓ _>_ y) → ↓ _>_ x

↓𝔹 : ∀ {l} {A : Set l} (_>_ : A → A → 𝔹) → A → Set l
↓𝔹 {l} _>_ x = ↓ {l} {lzero} (λ x y → (x > y) ≡ ⊤) x


↓-> : ∀ n → ↓𝔹 _>_ n
↓-> n = pf↓ (h n)
  where h : ∀ x → ∀ {y} → x > y ≡ ⊤ → ↓𝔹 _>_ y
        h 0 {0} ()
        h 0 {suc y} ()
        h (suc x) {y} p with <-drop {y} p
        h (suc x) {y} p | ⊤ , q rewrite q = ↓-> x
        h (suc x) {y} p | ⊥ , q = h x q


module measure {l l' l₁ l₂ : Level}
               {A : Set l} {B : Set l'}
               (_>A_ : A → A → Set l₁)
               (_>B_ : B → B → Set l₂)
               (m : A → B) (mono : ∀ {a a'} → a >A a' → m a >B m a') where

  measure-↓ : ∀ {a : A} → ↓ _>B_ (m a) → ↓ _>A_ a
  measure-↓ {a} (pf↓ fM) = pf↓ h
    where h : ∀ {y} → a >A y → ↓ _>A_ y
          h p = measure-↓ (fM (mono p))
