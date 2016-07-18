module One where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ b = b
(suc a) +ℕ b = suc (a +ℕ b)

_×ℕ_ : ℕ → ℕ → ℕ
zero ×ℕ b = zero
(suc a) ×ℕ b = b +ℕ (a ×ℕ b)
{-# BUILTIN NATURAL ℕ #-}


data List (X : Set) : Set where
  ⟨⟩   : List X
  _::_ : X → List X → List X

_++_ : ∀ {X} → List X → List X → List X
⟨⟩ ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


record Σ {l} (A : Set l) (B : A → Set l) : Set l where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

v_ : ∀ {l} {S : Set l}{T : S → Set l}{P : Σ S T → Set l} →
     ((s : S) → (t : T s) → P (s , t)) →
     (p : Σ S T) → P p
(v p) (s , t) = p s t

_×_ : ∀ {k} (A B : Set k) → Set k
A × B = Σ A (λ _ → B)

data One : Set where ⟨⟩ : One
data Two : Set where tt ff : Two

_⟨?⟩_ : ∀ {l} {P : Two → Set l} → P tt → P ff → (p : Two) → P p
(s ⟨?⟩ t) tt = s
(s ⟨?⟩ t) ff = t

_+_ : Set → Set → Set
S + T = Σ Two (S ⟨?⟩ T)


data Fin : ℕ → Set where
  zero' : {n : ℕ} → Fin (suc n)
  suc' : {n : ℕ} → Fin n → Fin (suc n)

fin : ∀ (n : ℕ) → Fin (suc n)
fin zero = zero'
fin (suc n) = suc' (fin n)


id : ∀ {k} {A : Set k} → A → A
id x = x

const : ∀ {k} {A B : Set k} → A → B → A
const x = λ _ → x

_∘_ : ∀ {k} {A B C : Set k} → (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)



data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A →  Vec A n → Vec A (suc n)

head : {n : ℕ} → {A : Set} → Vec A (suc n) → A
head (x :: _) = x

tail : {n : ℕ} → {A : Set} → Vec A (suc n) → Vec A n
tail (_ :: xs) = xs

vec : {n : ℕ} → {A : Set} → A → Vec A n
vec {zero} x = []
vec {suc n} x = x :: vec x

vapp : {n : ℕ} → {S T : Set} → Vec (S → T) n → Vec S n → Vec T n
vapp [] [] = []
vapp (f :: fs) (s :: ss) = f s :: vapp fs ss

vmap : {n : ℕ} → {S T : Set} → (S → T) → Vec S n → Vec T n
vmap f xs = vapp (vec f) xs

zip : {n : ℕ} → {A B : Set} →  Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

zip' : {n : ℕ} → {S T : Set} →  Vec S n → Vec T n → Vec (S × T) n
zip' as bs = vapp (vapp (vec _,_) as) bs

append : {n m : ℕ} → {A : Set} → Vec A n → Vec A m → Vec A (n +ℕ m)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

concat : {n m : ℕ} → {A : Set} → Vec (Vec A m) n → Vec A (n ×ℕ m)
concat [] = []
concat (xs :: xss) = append xs (concat xss)


proj : {n : ℕ} → {X : Set} → Vec X n → Fin n → X
proj (x :: xs) zero' = x
proj (x :: xs) (suc' i) = proj xs i

tabulate : {n : ℕ} → {X : Set} → (Fin n → X) → Vec X n
tabulate {zero} f = []
tabulate {suc n} f = f zero' :: tabulate (λ _ → f zero')


diagonal : {n : ℕ} → {A : Set} → Vec (Vec A n) n → Vec A n
diagonal [] = []
diagonal (xs :: xss) = head xs :: diagonal (vmap tail xss)


snoc : {n : ℕ} → {A : Set} → Vec A n → A → Vec A (suc n)
snoc [] y = y :: []
snoc (x :: xs) y = x :: snoc xs y

reverse : {n : ℕ} → {A : Set} → Vec A n → Vec A n
reverse [] = []
reverse (x :: xs) = snoc (reverse xs) x


mapp : {n m : ℕ} → {A B : Set} → Vec (Vec (A → B) n) m → Vec (Vec A n) m → Vec (Vec B n) m
mapp [] [] = []
mapp (f :: fs) (x :: xs) = vapp f x :: mapp fs xs

mapp' : {n m : ℕ} → {A B : Set} → Vec (Vec (A → B) n) n → Vec (Vec A n) n → Vec (Vec B n) n
mapp' fm xm = vapp (vapp (vec vapp) fm) xm



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
endoFunctorId = record {map = λ f x → f x}
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
  infixr 4 _∙_
  field
    ε : X
    _∙_ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative = record {pure = λ _ → ε; _⊛_ = _∙_}
open Monoid {{...}} public

instance monoidNat : Monoid ℕ
monoidNat = record {ε = zero ; _∙_ = _+ℕ_ }


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

record Normal : Set1 where
  constructor _/_
  field
    Shape : Set
    size :  Shape → ℕ
  [_]ₙ   : Set → Set
  [ X ]ₙ = Σ Shape λ s → Vec X (size s)
open Normal public
infixr 0 _/_

VecN : ℕ → Normal
VecN n = One / const n -- We don't have the ((→) r) Applicative, Conor!
ListN : Normal
ListN = ℕ / id

Kₙ : Set → Normal
Kₙ A = A / (λ _ → 0)
IKₙ : Normal
IKₙ = VecN 1

_+ₙ_ : Normal → Normal → Normal
(ShF / szF) +ₙ (ShG / szG) = (ShF + ShG) / v (szF ⟨?⟩ szG)

_×ₙ_ : Normal → Normal → Normal
(ShF / szF) ×ₙ (ShG / szG) = (ShF × ShG) / v (λ f g → szF f +ℕ szG g)

nlnj : ∀ {X} (F G : Normal) → [ F ]ₙ X + [ G ]ₙ X → [ F +ₙ G ]ₙ X
nlnj F G (tt , (ShF , xs)) = (tt , ShF) , xs
nlnj F G (ff , (ShG , xs)) = (ff , ShG) , xs


data _≃_ {l} {X : Set l} (x : X) : X → Set l where
  refl : x ≃ x
infix 1 _≃_

subst : ∀ {k l} {X : Set k} {s t : X} →
        s ≃ t → (P : X → Set l) → P s → P t
subst refl P p = p

{-# BUILTIN EQUALITY _≃_ #-}
{-# BUILTIN REFL refl #-}

record MonoidOk X {{M : Monoid X}} : Set where
  field
    absorbL : (x : X) → ε ∙ x ≃ x
    absorbR : (x : X) → x ∙ ε ≃ x
    assoc   : (x y z : X) → (x ∙ y) ∙ z ≃ x ∙ (y ∙ z)
open MonoidOk {{...}} public

natMonoidOk : MonoidOk ℕ
natMonoidOk = record
  { absorbL = λ _ → refl
  ; absorbR = _+zero
  ; assoc   = assoc+
  } where
    _+zero : ∀ x → x +ℕ zero ≃ x
    zero +zero = refl
    suc n +zero rewrite n +zero = refl

    assoc+ : ∀ x y z → (x +ℕ y) +ℕ z ≃ x +ℕ (y +ℕ z)
    assoc+ zero y z = refl
    assoc+ (suc x) y z rewrite assoc+ x y z = refl


instance listMonoid : ∀ {X} → Monoid (List X)
listMonoid = λ {X} → record { ε = ⟨⟩ ; _∙_ = _++_ }

listMonoidOk : ∀ {X} → MonoidOk (List X)
listMonoidOk = record
  { absorbL = λ _ → refl
  ; absorbR = _++⟨⟩
  ; assoc   = assoc++
  } where
    _++⟨⟩ : ∀ x → x ++ ⟨⟩ ≃ x
    ⟨⟩ ++⟨⟩ = refl
    (x :: xs) ++⟨⟩ rewrite xs ++⟨⟩ = refl

    assoc++ : ∀ x y z → (x ++ y) ++ z ≃ x ++ (y ++ z)
    assoc++ ⟨⟩ y z = refl
    assoc++ (x :: x₁) y z rewrite assoc++ x₁ y z = refl
