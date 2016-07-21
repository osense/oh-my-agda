module Two where
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Function using (_∘_)

data Unit : Set where ⟨⟩ : Unit

data ★ : Set where
  ι   : ★
  _⊳_ : ★ → ★ → ★
infixr 5 _⊳_

data Cx (X : Set) : Set where
  ε   : Cx X
  _⹁_ : Cx X → X → Cx X
infixl 4 _⹁_

data _∈_ (τ : ★) : Cx ★ → Set where
  zero : ∀ {Γ} → τ ∈ Γ ⹁ τ
  suc  : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ ⹁ σ
infix 3 _∈_

data _⊢_ (Γ : Cx ★) : ★ → Set where
  var : ∀ {τ} → τ ∈ Γ → Γ ⊢ τ
  lam : ∀ {σ τ} → Γ ⹁ σ ⊢ τ → Γ ⊢ σ ⊳ τ
  app : ∀ {σ τ} → Γ ⊢ σ ⊳ τ → Γ ⊢ σ → Γ ⊢ τ
infix 3 _⊢_


⟦_⟧★ : ★ → Set
⟦ ι ⟧★ = ℕ
⟦ σ ⊳ τ ⟧★ = ⟦ σ ⟧★ → ⟦ τ ⟧★

⟦_⟧Cx : Cx ★ → (★ → Set) → Set
⟦ ε ⟧Cx V = Unit
⟦ Γ ⹁ σ ⟧Cx V = (⟦ Γ ⟧Cx V) × (V σ)

⟦_⟧∈ : ∀ {Γ τ V} → τ ∈ Γ → ⟦ Γ ⟧Cx V → V τ
⟦ zero ⟧∈ (γ , t) = t
⟦ suc i ⟧∈  (γ , s) = ⟦ i ⟧∈ γ

⟦_⟧⊢ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧Cx ⟦_⟧★ → ⟦ τ ⟧★
⟦ var i ⟧⊢ γ = ⟦ i ⟧∈ γ
⟦ lam t ⟧⊢ γ = λ s → ⟦ t ⟧⊢ (γ , s)
⟦ app f s ⟧⊢  γ = ⟦ f ⟧⊢ γ (⟦ s ⟧⊢ γ)


Ren Sub : Cx ★ → Cx ★ → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

_<><_ : ∀ {X} → Cx X → List X → Cx X
xz <>< [] = xz
xz <>< (x ∷ xs) =  xz ⹁ x <>< xs 
infixl 4 _<><_

Shub : Cx ★ → Cx ★ → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var i = θ [] i
θ // lam t = lam (((λ As → θ (_ ∷ As))) // t)
θ // app f s = app (θ // f) (θ // s)
