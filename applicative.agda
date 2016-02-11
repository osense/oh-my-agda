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
    _⊛_  : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {map = _⊛_ ∘ pure}
open Applicative {{...}} public

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {X} → X → F X
    _>>=_  : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative = record
    {pure = return
    ;_⊛_  = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)}
open Monad {{...}} public


instance applicativeVec : ∀ {n : ℕ} → Applicative λ X → Vec X n
applicativeVec = record {pure = vec; _⊛_ = vapp}
endoFunctorVec : ∀ {n : ℕ} → EndoFunctor λ X → Vec X n
endoFunctorVec = applicativeEndoFunctor
monadVec : ∀ {n : ℕ} → Monad λ X → Vec X n
monadVec = record {return = pure; _>>=_ = λ xs f → diagonal (vmap f xs)}


instance endoFunctorId : EndoFunctor id
endoFunctorId = record {map = _$_}
applicativeId : Applicative id
applicativeId = record {pure = id; _⊛_ = map}


applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp F G = record
  {pure = Applicative.pure F ∘ Applicative.pure G
  ;_⊛_  = let pureF = Applicative.pure F in
          let apF = Applicative._⊛_ F in
          let apG = Applicative._⊛_ G in
          λ f x → apF (apF (pureF apG) f) x}


record Monoid (X : Set) : Set where
  infixr 4 ∙
  field
    ε : X
    ∙ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative = record {pure = λ _ → ε; _⊛_ = ∙}
open Monoid {{...}} public
