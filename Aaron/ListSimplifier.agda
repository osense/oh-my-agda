module ListSimplifier where

open import List
open import Relation using (_≡_; refl; inspect; _with≡_; sym; cong₂)
open import Nat using (ℕ; suc)
open import Bool using (𝔹; ⊤; ⊥)
open import Product using (_∘_)

data Listʳ : Set → Set₁ where
  _ʳ    : ∀ {A} → List A → Listʳ A
  _++ʳ_ : ∀ {A} → Listʳ A → Listʳ A → Listʳ A
  mapʳ  : ∀ {A B} → (A → B) → Listʳ A → Listʳ B
  _::ʳ_ : ∀ {A} → A → Listʳ A → Listʳ A
  []ʳ   : ∀ {A} → Listʳ A


⟦_⟧ : ∀ {A} → Listʳ A → List A
⟦ l ʳ ⟧       = l
⟦ l₁ ++ʳ l₂ ⟧ = ⟦ l₁ ⟧ ++ ⟦ l₂ ⟧
⟦ mapʳ x l ⟧  = map x ⟦ l ⟧
⟦ x ::ʳ l ⟧   = x :: ⟦ l ⟧
⟦ []ʳ ⟧       = []


is-emptyʳ : ∀ {A} → Listʳ A → 𝔹
is-emptyʳ []ʳ = ⊤
is-emptyʳ _ = ⊥

is-emptyʳ-≡ : ∀ {A} → (l : Listʳ A) → is-emptyʳ l ≡ ⊤ → l ≡ []ʳ
is-emptyʳ-≡ []ʳ p = refl
is-emptyʳ-≡ (x ʳ) ()
is-emptyʳ-≡ (l ++ʳ l₁) ()
is-emptyʳ-≡ (mapʳ x l) ()
is-emptyʳ-≡ (x ::ʳ l) ()


step : ∀ {A} → Listʳ A → Listʳ A
step ((l₁ ++ʳ l₂) ++ʳ l₃) = l₁ ++ʳ (l₂ ++ʳ l₃)
step ((x ::ʳ l₁) ++ʳ l₂) = x ::ʳ (l₁ ++ʳ l₂)
step ([]ʳ ++ʳ l) = l
step ((l ʳ) ++ʳ l') with is-emptyʳ l'
step ((l ʳ) ++ʳ l') | ⊤ = l ʳ
step ((l ʳ) ++ʳ l') | ⊥ = (l ʳ) ++ʳ l'
step ((mapʳ f l₁) ++ʳ l₂) with is-emptyʳ l₂
step ((mapʳ f l₁) ++ʳ l₂) | ⊤ = mapʳ f l₁
step ((mapʳ f l₁) ++ʳ l₂) | ⊥ = (mapʳ f l₁) ++ʳ l₂
step (mapʳ f (l₁ ++ʳ l₂)) = (mapʳ f l₁) ++ʳ (mapʳ f l₂)
step (mapʳ f (l ʳ)) = (map f l)ʳ
step (mapʳ f (mapʳ g l)) = mapʳ (f ∘ g) l
step (mapʳ f (x ::ʳ l)) = (f x) ::ʳ (mapʳ f l)
step (mapʳ f []ʳ) = []ʳ
step (l ʳ) = l ʳ
step (x ::ʳ l) = x ::ʳ l
step []ʳ = []ʳ

superdev : ∀ {A} → Listʳ A → Listʳ A
superdev (x ʳ) = x ʳ
superdev (l₁ ++ʳ l₂) = step ((superdev l₁) ++ʳ (superdev l₂))
superdev (mapʳ x l) = step (mapʳ x (superdev l))
superdev (x ::ʳ l) = step (x ::ʳ (superdev l))
superdev []ʳ = []ʳ

simplify : ∀ {A} → Listʳ A → ℕ → Listʳ A
simplify l 0 = l
simplify l (suc n) = simplify (superdev l) n


step-sound : ∀ {A} → (l : Listʳ A) → ⟦ l ⟧ ≡ ⟦ step l ⟧
step-sound ((l₁ ++ʳ l₂) ++ʳ l₃) = ++-assoc ⟦ l₁ ⟧ ⟦ l₂ ⟧ ⟦ l₃ ⟧
step-sound ((x ::ʳ l₁) ++ʳ l₂)  = refl
step-sound ([]ʳ ++ʳ l)          = refl
step-sound ((l ʳ) ++ʳ l') with inspect (is-emptyʳ l')
step-sound ((l ʳ) ++ʳ l') | ⊤ with≡ p rewrite p | is-emptyʳ-≡ l' p = ++-[] l
step-sound ((l ʳ) ++ʳ l') | ⊥ with≡ p rewrite p                    = refl
step-sound ((mapʳ f l₁) ++ʳ l₂) with inspect (is-emptyʳ l₂)
step-sound ((mapʳ f l₁) ++ʳ l₂) | ⊤ with≡ p rewrite p | is-emptyʳ-≡ l₂ p = ++-[] (map f ⟦ l₁ ⟧)
step-sound ((mapʳ f l₁) ++ʳ l₂) | ⊥ with≡ p rewrite p                    = refl
step-sound (mapʳ f (l₁ ++ʳ l₂)) = map-++ f ⟦ l₁ ⟧ ⟦ l₂ ⟧
step-sound (mapʳ f (l ʳ))       = refl
step-sound (mapʳ f (mapʳ g l))  = map-∘ f g ⟦ l ⟧
step-sound (mapʳ f (x ::ʳ l))   = refl
step-sound (mapʳ f []ʳ)         = refl
step-sound (l ʳ)                = refl
step-sound (x ::ʳ l)            = refl
step-sound []ʳ                  = refl

superdev-sound : ∀ {A} → (l : Listʳ A) → ⟦ l ⟧ ≡ ⟦ superdev l ⟧
superdev-sound (x ʳ) = refl
superdev-sound (l₁ ++ʳ l₂) rewrite sym (step-sound (superdev l₁ ++ʳ superdev l₂)) = cong₂ _++_ (superdev-sound l₁) (superdev-sound l₂)
superdev-sound (mapʳ x l) rewrite sym (step-sound (mapʳ x (superdev l))) = cong₂ map refl (superdev-sound l)
superdev-sound (x ::ʳ l) = cong₂ _::_ refl (superdev-sound l)
superdev-sound []ʳ = refl

sound : ∀ {A} → (l : Listʳ A) → (n : ℕ) → ⟦ l ⟧ ≡ ⟦ simplify l n ⟧
sound l 0 = refl
sound l (suc n) rewrite superdev-sound l = sound (superdev l) n
