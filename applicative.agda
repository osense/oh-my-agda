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
instance applicativeId : Applicative id
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


applicativePointwise : ∀ {F G} {X : Set} → Applicative F → Applicative G → Applicative (λ X → (F X) × (G X))
applicativePointwise F G = record
  {pure = λ x → pure x , pure x
  ;_⊛_ = λ h x → (fst h ⊛ fst x) , (snd h ⊛ snd x)}


record Traversable (F : Set → Set) : Set1 where
  field
    traverse : ∀ {G S T} {{_ : Applicative G}} → (S → G T) → F S → G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record {map = traverse}
open Traversable {{...}} public

instance traversableVec : {n : ℕ} → Traversable λ X → Vec X n
traversableVec = record {traverse = vtr} where
  vtr : ∀ {n G S T} {{_ : Applicative G}} → (S → G T) → Vec S n → G (Vec T n)
  vtr {{aG}} f [] = pure {{aG}} []
  vtr {{aG}} f (s :: ss) = pure {{aG}} _::_ ⊛ f s ⊛ vtr f ss

transpose : ∀ {n m X} → Vec (Vec X n) m → Vec (Vec X m) n
transpose = traverse id
