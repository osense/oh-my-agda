module Kripke where

open import String
open import List using (List; []; _::_)
open import Bool using (⊤; ⊥; if_then_else)
open import Relation using (_≡_; refl; Unit; reflexiveS; transitiveS)
open import Product using (_×_; _,_; fst; snd)


data Formula : Set where
  $ : String → Formula
  true : Formula
  _implies_ _and_ : Formula → Formula → Formula

Ctx : Set
Ctx = List Formula

data _⊢_ : Ctx → Formula → Set where
  assume : ∀ {Γ f} → f :: Γ ⊢ f
  weaken : ∀ {Γ f f'} → Γ ⊢ f → f' :: Γ ⊢ f
  truth  : ∀ {Γ} → Γ ⊢ true
  andI   : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ → Γ ⊢ f₂ → Γ ⊢ f₁ and f₂
  andE   : ∀ {Γ f₁ f₂} b → Γ ⊢ f₁ and f₂ → Γ ⊢ if b then f₁ else f₂
  implI  : ∀ {Γ f f'} → f :: Γ ⊢ f' → Γ ⊢ f implies f'
  implE  : ∀ {Γ f f'} → Γ ⊢ f implies f' → Γ ⊢ f  → Γ ⊢ f'
infixr 5 _⊢_

record Struct : Set₁ where
  field
    W      : Set
    R      : W → W → Set
    reflR  : reflexiveS R
    transR : transitiveS R
    V      : W → String → Set
    monoV  : ∀ {w w'} → R w w' → ∀ {i} → V w i → V w' i
open Struct

_,_⊨_ : ∀ (k : Struct) → W k → Formula → Set
k , w ⊨ $ x = (V k) w x
k , w ⊨ true = Unit
k , w ⊨ (f implies f') = ∀ {w' : W k} → (R k) w w' → k , w' ⊨ f → k , w' ⊨ f'
k , w ⊨ (f₁ and f₂) = (k , w ⊨ f₁) × (k , w ⊨ f₂)

_,_⊨Ctx_ : ∀ (k : Struct) → W k → Ctx → Set
k , w ⊨Ctx [] = Unit
k , w ⊨Ctx (x :: l) = (k , w ⊨ x) × (k , w ⊨Ctx l)


mono⊨ : ∀ {k : Struct} {w w' : W k} {f : Formula} → (R k) w w' →  k , w ⊨ f → k , w' ⊨ f
mono⊨ {k} {f = $ x} r p = (monoV k) r p
mono⊨ {k} {f = true} r p = Unit.U
mono⊨ {k} {f = f implies f₁} r p r' p' = p ((transR k) r r') p'
mono⊨ {k} {f = f₁ and f₂} r (p₁ , p₂) = (mono⊨ {f = f₁} r p₁) , (mono⊨ {f = f₂} r p₂)

mono⊨Ctx : ∀ {k : Struct} {w w' : W k} {c : Ctx} → (R k) w w' → k , w ⊨Ctx c → k , w' ⊨Ctx c
mono⊨Ctx {c = []} r p = Unit.U
mono⊨Ctx {c = x :: c} r (p , t) = (mono⊨ {f = x} r p) , mono⊨Ctx r t


_⊩_ : Ctx → Formula → Set₁
Γ ⊩ f = ∀ {k : Struct} {w : W k} → k , w ⊨Ctx Γ → k , w ⊨ f

soundness : ∀ {Γ f} → Γ ⊢ f → Γ ⊩ f
soundness assume c = fst c
soundness (weaken p) c = soundness p (snd c)
soundness truth c = Unit.U
soundness (andI p₁ p₂) c = (soundness p₁ c) , (soundness p₂ c)
soundness (andE ⊤ p) c = fst (soundness p c)
soundness (andE ⊥ p) c = snd (soundness p c)
soundness (implI p) c r' p' = soundness p (p' , mono⊨Ctx r' c)
soundness (implE p p') {k} c = soundness p c (reflR k) (soundness p' c)
