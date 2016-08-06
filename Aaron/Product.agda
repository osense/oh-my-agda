module Product where

open import Bool using (𝔹; if_then_else)


record Σ {l} (A : Set l) (B : A → Set l) : Set l where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public
infixr 6 _,_

_×_ : ∀ {l} (A B : Set l) → Set l
a × b = Σ a (λ _ → b)
infixr 6 _×_

_+_ : (A B : Set) → Set
a + b = Σ 𝔹 (λ x → if x then a else b)


-- Function is sort of a product, right?
_∘_ : ∀ {l} {A B C : Set l} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)


data Maybe {l} (A : Set l) : Set l where
  nothing : Maybe A
  just : (a : A) → Maybe A
