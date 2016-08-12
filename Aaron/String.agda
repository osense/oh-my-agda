module String where

open import Bool using (𝔹)


postulate
  String : Set

{-# BUILTIN STRING String #-}

private
  primitive
    primStringEquality : String → String → 𝔹

_==_ : String → String → 𝔹
_==_ = primStringEquality
