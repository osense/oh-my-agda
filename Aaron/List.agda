module List where

open import Nat using (ℕ; zero; suc; _+_; _≤_; ≤-trans; ≤-suc)
open import Bool
open import Relation using (_≡_; refl; cong₂; inspect; _with≡_)

data List {l} (A : Set l) : Set l where
  [] : List A
  _::_ : (x : A) → List A → List A
infixr 6 _::_


length : ∀ {l} {A : Set l} → List A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

_++_ : ∀ {l} {A : Set l} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {l l'} {A : Set l} {B : Set l'} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

fold : ∀ {l l'} {A : Set l} (P : List A → Set l') → (∀ {a l} → A → P l → P (a :: l)) → P [] → (l : List A) → P l
fold p f init [] = init
fold p f init (x :: xs) = f x (fold p f init xs)

filter : ∀ {l} {A : Set l} → (A → 𝔹) → List A → List A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in if p x then x :: r else r

snoc : ∀ {l} {A : Set l} → List A → A → List A
snoc [] y = y :: []
snoc (x :: xs) y = x :: snoc xs y

reverse : ∀ {l} {A : Set l} → List A → List A
reverse [] = []
reverse (x :: xs) = snoc (reverse xs) x

repeat : ∀ {l} {A : Set l} → ℕ → A → List A
repeat zero x = []
repeat (suc n) x = x :: repeat n x

takeWhile : ∀ {l} {A : Set l} → (p : A → 𝔹) → List A → List A
takeWhile p [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

take : ∀ {l} {A : Set l} → ℕ → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs

nthTail : ∀ {l} {A : Set l} → ℕ → List A → List A
nthTail zero xs = xs
nthTail (suc n) [] = []
nthTail (suc n) (x :: xs) = nthTail n xs


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


filter-idem : ∀ {l} {A : Set l} → (p : A → 𝔹) → (l : List A) → filter p (filter p l) ≡ filter p l
filter-idem p [] = refl
filter-idem p (x :: l) with inspect (p x)
filter-idem p (x :: l) | ⊤ with≡ q rewrite q | q | filter-idem p l = refl
filter-idem p (x :: l) | ⊥ with≡ q rewrite q | q | filter-idem p l = refl

snoc-length : ∀ {l} {A : Set l} → (l : List A) → (x : A) → length (snoc l x) ≡ suc (length l)
snoc-length [] y = refl
snoc-length (x :: xs) y rewrite snoc-length xs y = refl

reverse-length : ∀ {l} {A : Set l} → (l : List A) → length (reverse l) ≡ length l
reverse-length [] = refl
reverse-length (x :: xs) rewrite snoc-length (reverse xs) x | reverse-length xs = refl

repeat-filter : ∀ {l} {A : Set l} {p : A → 𝔹} {a : A} {n : ℕ} → p a ≡ ⊥ → filter p (repeat n a) ≡ []
repeat-filter {n = 0} pf = refl
repeat-filter {n = suc n'} pf rewrite pf = repeat-filter {n = n'} pf

++-filter : ∀ {l} {A : Set l} (p : A → 𝔹) → (l₁ l₂ : List A) → filter p (l₁ ++ l₂) ≡ (filter p l₁) ++ (filter p l₂)
++-filter p [] l₂ = refl
++-filter p (x :: l₁) l₂ with (p x)
++-filter p (x :: l₁) l₂ | ⊤ rewrite ++-filter p l₁ l₂ = refl
++-filter p (x :: l₁) l₂ | ⊥ = ++-filter p l₁ l₂

takeWhile-repeat : ∀ {l} {A : Set l} {p : A → 𝔹} {a : A} {n : ℕ} → p a ≡ ⊤ → takeWhile p (repeat n a) ≡ repeat n a
takeWhile-repeat {n = 0} pf = refl
takeWhile-repeat {n = suc n'} pf rewrite pf = cong₂ _::_ refl (takeWhile-repeat {n = n'} pf)

take-nthTail : ∀ {l} {A : Set l} {n : ℕ} → (l : List A) → (take n l) ++ (nthTail n l) ≡ l
take-nthTail {n = 0} xs = refl
take-nthTail {n = suc n} [] = refl
take-nthTail {n = suc n} (x :: xs) rewrite take-nthTail {n = n} xs = refl
