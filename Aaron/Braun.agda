open import Agda.Primitive using (_⊔_)
open import Relation using (_≡_; refl; sym)
open import Product using (_×_; _,_)
open import Nat using (ℕ; suc; zero; _+_; suc-inj; +0; +suc; +comm)
open import Bool
open import List using (List; []; _::_; length; fold)

module Braun {l} (A : Set l) (_<A_ : A → A → 𝔹) where



data _⊎_ {l l'} (A : Set l) (B : Set l') : Set (l ⊔ l') where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (x : B) → A ⊎ B


data BraunT : (n : ℕ) → Set l where
  empty : BraunT 0
  node  : ∀ {n m : ℕ} → A → BraunT n → BraunT m →
          (n ≡ m) ⊎ (n ≡ suc m) →
          BraunT (suc (n + m))


insert : ∀ {n} → A → BraunT n → BraunT (suc n)
insert a empty = node a empty empty (inj₁ refl)
insert a (node {n} {m} a' l r p) rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
insert a (node {n} {m} a' l r _) | inj₁ p | (a₁ , a₂) rewrite p = node a₁ (insert a₂ r) l (inj₂ refl)
insert a (node {n} {m} a' l r _) | inj₂ p | (a₁ , a₂) = node a₁ (insert a₂ r) l (inj₁ (sym p))

contains : ∀ {n} → A → BraunT n → 𝔹
contains a empty = ⊥
contains a (node x l r p) = if a ≃ x then ⊤ else ((contains a l) ∨ (contains a r))
  where _≃_ : A → A → 𝔹
        a ≃ b = (a <A b) ∧ (b <A a)

remove-min : ∀ {n} → BraunT (suc n) → A × BraunT n
remove-min (node a empty empty p) = a , empty
remove-min (node a empty (node _ _ _ _) (inj₁ ()))
remove-min (node a empty (node _ _ _ _) (inj₂ ()))
remove-min (node a (node {n₁} {m₁} a₁ l₁ r₁ p₁) empty p) rewrite +0 (n₁ + m₁) = a , node a₁ l₁ r₁ p₁
remove-min (node a (node a₁ l₁ r₁ p₁) (node a₂ l₂ r₂ p₂) p)
  with remove-min (node a₁ l₁ r₁ p₁) | if a₁ <A a₂ then (a₁ , a₂) else (a₂ , a₁)
remove-min (node a (node {n₁} {m₁} a₁ l₁ r₁ p₁) (node {n₂} {m₂} a₂ l₂ r₂ p₂) p) | (_ , l₁') | (smaller , larger) -- _ must be a₁
  rewrite +suc (n₁ + m₁) (n₂ + m₂) | +comm (n₁ + m₁) (n₂ + m₂) = a , node smaller (node larger l₂ r₂ p₂) l₁' (lemma p)
  where lemma : ∀ {x y} → (suc x ≡ y) ⊎ (suc x ≡ suc y) → (y ≡ x) ⊎ (y ≡ suc x)
        lemma (inj₁ p) = inj₂ (sym p)
        lemma (inj₂ p) = inj₁ (suc-inj (sym p))


list-to-braun : (l : List A) → BraunT (length l)
list-to-braun xs = fold (λ l → BraunT (length l)) insert empty xs

merge : List A → List A → List A
merge [] ys = ys
merge xs [] = xs
merge (x :: xs) (y :: ys) with x <A y
merge (x :: xs) (y :: ys) | ⊤ = x :: (merge xs (y :: ys))
merge (x :: xs) (y :: ys) | ⊥ = y :: (merge (x :: xs) ys)

merge-sort : List A → List A
merge-sort l = msort (list-to-braun l)
  where msort : ∀ {n} → BraunT n → List A
        msort empty = []
        msort (node x l r p) = merge (x :: (msort l)) (msort r)
