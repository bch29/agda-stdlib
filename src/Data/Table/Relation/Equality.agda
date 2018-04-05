------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise table equality
------------------------------------------------------------------------

module Data.Table.Relation.Equality where

open import Relation.Binary using (Rel; Setoid)
open import Data.Table.Base
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_)

Pointwise : ∀ {n} {a ℓ} {A : Set a} → Rel A ℓ → Rel (Table A n) ℓ
Pointwise _∼_ t t′ = ∀ i → lookup t i ∼ lookup t′ i

module _ {c p} (S : Setoid c p) where
  open Setoid S

  setoid : ℕ → Setoid _ _
  setoid n = record
    { Carrier = Table Carrier n
    ; _≈_ = Pointwise _≈_
    ; isEquivalence = record
      { refl  = λ i → refl
      ; sym   = λ p → sym ∘ p
      ; trans = λ p q i → trans (p i) (q i)
      }
    }

  tail-cong : ∀ {n} {t t′ : Table Carrier (suc n)} → Pointwise _≈_ t t′ → Pointwise _≈_ (tail t) (tail t′)
  tail-cong eq = eq ∘ suc

≡-setoid : ∀ {a} → Set a → ℕ → Setoid _ _
≡-setoid A = setoid (P.setoid A)

module _ {a} {A : Set a} {n} where
  open Setoid (≡-setoid A n) public
    using () renaming (_≈_ to _≗_)
