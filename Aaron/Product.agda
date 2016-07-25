module Product where


record Σ {l} (A : Set l) (B : A → Set l) : Set l where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public


data Maybe {l} (A : Set l) : Set l where
  nothing : Maybe A
  just : (a : A) → Maybe A
