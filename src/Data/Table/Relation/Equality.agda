------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise table equality
------------------------------------------------------------------------

module Data.Table.Relation.Equality where

open import Relation.Binary using (REL; Rel; Setoid)
open import Data.Table.Base
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

Pointwise : ∀ {n} {a ℓ} {A : Set a} → Rel A ℓ → Rel (Table A n) ℓ
Pointwise _∼_ t t′ = ∀ i → lookup t i ∼ lookup t′ i

Pointwise′ : ∀ {m n} {a a′ ℓ} {A : Set a} {A′ : Set a′} → REL A A′ ℓ → REL (Table A m) (Table A′ n) ℓ
Pointwise′ {m} {n} _∼_ t t′ = m ≡ n × ∀ i i′ → i ≅ i′ → lookup t i ∼ lookup t′ i′

Pointwise⇒Pointwise′ : ∀ {n} {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) {t t′ : Table A n} → Pointwise _∼_ t t′ → Pointwise′ _∼_ t t′
Pointwise⇒Pointwise′ _∼_ p = P.refl , (λ {i .i H.refl → p i})

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

  foldr-cong : ∀ {n} {_∙_ : Carrier → Carrier → Carrier} {z} →
    (∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ∙ y) ≈ (x′ ∙ y′)) →
    {t t′ : Table Carrier n} →
    Pointwise _≈_ t t′ →
    foldr _∙_ z t ≈ foldr _∙_ z t′
  foldr-cong {zero} {_∙_} ∙-cong {t} {t′} t≈t′ = refl
  foldr-cong {suc n} {_∙_} ∙-cong {t} {t′} t≈t′ = ∙-cong (t≈t′ zero) (foldr-cong ∙-cong (tail-cong t≈t′))

≡-setoid : ∀ {a} → Set a → ℕ → Setoid _ _
≡-setoid A = setoid (P.setoid A)

module _ {a} {A : Set a} {n} where
  open Setoid (≡-setoid A n) public
    using () renaming (_≈_ to _≗_)
