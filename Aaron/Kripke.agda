module Kripke where

open import String
open import List using (List; []; _::_)
open import Bool using (⊤; ⊥; if_then_else)
open import Relation using (_≡_; refl; Unit; Empty; reflexiveS; transitiveS)
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



data _⪯_ : Ctx → Ctx → Set where
  ⪯-refl : ∀ {Γ} → Γ ⪯ Γ
  ⪯-cons : ∀ {Γ Δ f} → Γ ⪯ Δ → Γ ⪯ (f :: Δ)

⪯-trans : ∀ {Γ Δ Ε} → Γ ⪯ Δ → Δ ⪯ Ε → Γ ⪯ Ε
⪯-trans p₁ ⪯-refl = p₁
⪯-trans p₁ (⪯-cons p₂) = ⪯-cons (⪯-trans p₁ p₂)

weaken⪯ : ∀ {Γ Δ f} → Γ ⪯ Δ → Γ ⊢ f → Δ ⊢ f
weaken⪯ ⪯-refl p = p
weaken⪯ (⪯-cons e) p = weaken (weaken⪯ e p)

U : Struct
U = record {W = Ctx
           ;R = _⪯_
           ;reflR = ⪯-refl
           ;transR = ⪯-trans
           ;V = λ Γ p → Γ ⊢ ($ p)
           ;monoV = λ e p → weaken⪯ e p}


completenessU : ∀ {f Γ} → U , Γ ⊨ f → Γ ⊢ f
soundnessU    : ∀ {f Γ} → Γ ⊢ f → U , Γ ⊨ f
completenessU {$ x} u = u
completenessU {true} u = truth
completenessU {f₁ and f₂} u = andI (completenessU {f₁} (fst u)) (completenessU {f₂} (snd u))
completenessU {f implies f'} {Γ} u = implI (completenessU {f'}
                                       (u (⪯-cons ⪯-refl) (soundnessU {f} (assume {Γ}))))
soundnessU {$ x} p = p
soundnessU {true} p = Unit.U
soundnessU {f₁ and f₂} p = (soundnessU {f₁} (andE ⊤ p)) , (soundnessU {f₂} (andE ⊥ p))
soundnessU {f implies f₁} p r u = soundnessU (implE (weaken⪯ r p) ((completenessU {f} u)))


ctx-id : ∀ {Γ} → U , Γ ⊨Ctx Γ
ctx-id {[]} = Unit.U
ctx-id {f :: Γ} = (soundnessU {f} assume) , mono⊨Ctx (⪯-cons ⪯-refl) (ctx-id {Γ})

completeness : ∀ {Γ f} → Γ ⊩ f → Γ ⊢ f
completeness {Γ} p = completenessU (p {U} {Γ} (ctx-id {Γ}))

universality : ∀ {Γ f} → Γ ⊩ f → U , Γ ⊨ f
universality {Γ} {f} p = soundnessU (completeness {Γ} {f} p)

universalityʳ : ∀ {Γ f} → U , Γ ⊨ f → Γ ⊩ f
universalityʳ {Γ} {f} p = soundness (completenessU {f} {Γ} p)


nbe : ∀ {Γ f} → Γ ⊢ f → Γ ⊢ f
nbe p = completeness (soundness p)

a : [] ⊢ true
a = andE ⊤ (andI truth truth)
a' = nbe a

b : [] ⊢ true
b = implE (implE (implI (implI assume)) truth) truth
b' = nbe b

c : [] ⊢ (($ "p") implies ($ "p"))
c = implI (implE (implI assume) assume)
c' = nbe c

d : ($ "q") :: [] ⊢ ($ "p") implies ($ "q")
d = implI (implE (implI (weaken (weaken assume))) assume)
d' = nbe d

e : [] ⊢ ((($ "p") and ($ "q")) implies (($ "p") and ($ "q")))
e = implI assume
e' = nbe e

f : [] ⊢ (($ "p") implies ($ "q")) implies (($ "p") implies ($ "q"))
f = implI assume
f' = nbe f


-- conjunction associativity
g : [] ⊢ (($ "p") and (($ "q") and ($ "r"))) implies ((($ "p") and ($ "q")) and ($ "r"))
g = implI (andI
            (andI
              (andE ⊤ assume)
              (andE ⊤ (andE ⊥ assume)))
            (andE ⊥ (andE ⊥ assume)))
g-is-normal : g ≡ (nbe g)
g-is-normal = refl

-- function composition
h : [] ⊢ (($ "p") implies ($ "q")) implies ((($ "q") implies ($ "r")) implies (($ "p") implies ($ "r")))
h = implI (implI (implI (implE (weaken assume)
                               (implE (weaken (weaken assume))
                                      assume))))
h-is-normal : h ≡ (nbe h)
h-is-normal = refl

-- conjunction commutativity
i : (($ "p") and ($ "q")) :: [] ⊢ ($ "q") and ($ "p")
i = andI (andE ⊥ assume) (andE ⊤ assume)

-- same, without initial context
k : [] ⊢ (($ "p") and ($ "q")) implies (($ "q") and ($ "p"))
k = implI i

