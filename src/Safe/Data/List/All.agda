------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --safe #-}


module Safe.Data.List.All where

open import Safe.Data.List.Base as List hiding (map; tabulate; all)
open import Safe.Data.List.Any as Any using (here; there)
open import Safe.Data.List.Any.Membership.Propositional using (_∈_)
open import Safe.Function
open import Safe.Level
open import Safe.Relation.Nullary
import Safe.Relation.Nullary.Decidable as Dec
open import Safe.Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
open import Safe.Relation.Binary.PropositionalEquality

-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : List A → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

head : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} →
         All P xs → (∀ {x : A} → x ∈ xs → P x)
lookup []         ()
lookup (px ∷ pxs) (here refl)  = px
lookup (px ∷ pxs) (there x∈xs) = lookup pxs x∈xs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
           (∀ {x} → x ∈ xs → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp (here refl) ∷ tabulate (hyp ∘ there)

map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
      P ⋐ Q → All P ⋐ All Q
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

all : ∀ {a p} {A : Set a} {P : A → Set p} →
      Decidable P → Decidable (All P)
all p []       = yes []
all p (x ∷ xs) with p x
all p (x ∷ xs) | yes px = Dec.map′ (_∷_ px) tail (all p xs)
all p (x ∷ xs) | no ¬px = no (¬px ∘ head)