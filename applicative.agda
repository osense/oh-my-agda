module applicative where
open import basic
open import vector

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map : ∀ {S T} → (S → T) → F S → F T
open EndoFunctor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊛_
  field
    pure : ∀ {X} → X → F X
    _⊛_ : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {map = _⊛_ ∘ pure}
open Applicative {{...}} public

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {X} → X → F X
    _>>=_ : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative = record
    {pure = return
    ;_⊛_ = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)}
open Monad {{...}} public


endoFunctorVec : ∀ {n : ℕ} → EndoFunctor λ X → Vec X n
endoFunctorVec = record {map = vmap}

applicativeVec : ∀ {n : ℕ} → Applicative λ X → Vec X n
applicativeVec = record {pure = vec; _⊛_ = vapp}

monadVec : ∀ {n : ℕ} → Monad λ X → Vec X n
monadVec = record {return = vec; _>>=_ = λ xs f → diagonal (vmap f xs)}
