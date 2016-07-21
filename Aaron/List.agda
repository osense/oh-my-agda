module List where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Nat using (𝔹; ⊤; ⊥; if_then_else; ℕ; zero; suc; _+_; _≤_; ≤-trans; ≤-suc)

data List {l} (A : Set l) : Set l where
  [] : List A
  _::_ : (x : A) → List A → List A


length : ∀ {l} {A : Set l} → List A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

_++_ : ∀ {l} {A : Set l} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {l l'} {A : Set l} {B : Set l'} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀ {l} {A : Set l} → (A → 𝔹) → List A → List A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in if p x then x :: r else r


length-++ : ∀ {l} {A : Set l} (l₁ l₂ : List A) → length (l₁ ++ l₂) ≡ (length l₁) + (length l₂)
length-++ [] l₂ = refl
length-++ (x :: l₁) l₂ rewrite length-++ l₁ l₂ = refl

++-assoc : ∀ {l} {A : Set l} (l₁ l₂ l₃ : List A) → (l₁ ++ l₂) ++ l₃ ≡ l₁ ++ (l₂ ++ l₃)
++-assoc [] l₂ l₃ = refl
++-assoc (x :: l₁) l₂ l₃ rewrite ++-assoc l₁ l₂ l₃ = refl

length-filter : ∀ {l} {A : Set l} → (p : A → 𝔹) → (l : List A) → length (filter p l) ≤ length l ≡ ⊤
length-filter p [] = refl
length-filter p (x :: l) with p x
length-filter p (x :: l) | ⊤ = length-filter p l
length-filter p (x :: l) | ⊥ = ≤-trans {length (filter p l)} (length-filter p l) (≤-suc (length l))


data Singleton {l} {A : Set l} (x : A) : Set l where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {l} {A : Set l} (x : A) → Singleton x
inspect x = x with≡ refl

filter-idem : ∀ {l} {A : Set l} → (p : A → 𝔹) → (l : List A) → filter p (filter p l) ≡ filter p l
filter-idem p [] = refl
filter-idem p (x :: l) with inspect (p x)
filter-idem p (x :: l) | ⊤ with≡ q rewrite q | q | filter-idem p l = refl
filter-idem p (x :: l) | ⊥ with≡ q rewrite q | q | filter-idem p l = refl
