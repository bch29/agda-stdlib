------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

open import Algebra

module Algebra.Operations.CommutativeMonoid {s₁ s₂} (M : CommutativeMonoid s₁ s₂) where

open import Data.Nat.Base
  using (zero; suc; ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Fin using (Fin; zero)
open import Data.Table.Base as T using (Table; tabulate)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.EqReasoning as EqR

open CommutativeMonoid M
  renaming
    ( ε to 0#
    ; ∙-cong to +-cong
    ; identityʳ to +-identityʳ
    ; identityˡ to +-identityˡ
    ; assoc to +-assoc
    ; comm to +-comm
    )
open EqR setoid

------------------------------------------------------------------------
-- Operations

-- Viewing monoid concatenation as addition

private
  infixl 6 _+_

  _+_ = _∙_

-- Multiplication by natural number.

infixr 7 _×_ _×′_

_×_ : ℕ → Carrier → Carrier
0     × x = 0#
suc n × x = x + n × x

-- A variant that includes a "redundant" case which ensures that 1 × y
-- is definitionally equal to y.

_×′_ : ℕ → Carrier → Carrier
0     ×′ x = 0#
1     ×′ x = x
suc n ×′ x = x + n ×′ x

-- Summation over a list

sum : List Carrier → Carrier
sum = L.foldr _+_ 0#

-- A variant that sums every value of a function from a finite set.

sumTable : ∀ {n} → Table Carrier n → Carrier
sumTable {zero} _ = 0#
sumTable {suc n} t = Table.lookup t zero + sumTable (T.tail t)

-- An alternative mathematical-style syntax for sumTable

infixl 10 sumTable-syntax

sumTable-syntax : ∀ n → (Fin n → Carrier) → Carrier
sumTable-syntax _ = sumTable ∘ tabulate

syntax sumTable-syntax n (λ i → x) = ∑[ i < n ] x

------------------------------------------------------------------------
-- Some properties

-- Unfolding lemma for _×′_.

1+×′ : ∀ n x → suc n ×′ x ≈ x + n ×′ x
1+×′ 0 x = begin
  x       ≈⟨ sym $ +-identityʳ x ⟩
  x + 0#  ∎
1+×′ (suc n) x = begin
  x + suc n ×′ x  ≡⟨⟩
  x + suc n ×′ x  ∎

-- _×_ and _×′_ are extensionally equal (up to the setoid
-- equivalence).

×≈×′ : ∀ n x → n × x ≈ n ×′ x
×≈×′ 0       x = begin 0# ∎
×≈×′ (suc n) x = begin
  x + n × x   ≈⟨ +-cong refl (×≈×′ n x) ⟩
  x + n ×′ x  ≈⟨ sym $ 1+×′ n x ⟩
  suc n ×′ x  ∎

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-+ : ∀ c m n → (m ℕ+ n) × c ≈ m × c + n × c
×-homo-+ c 0 n = begin
  n × c       ≈⟨ sym $ +-identityˡ (n × c) ⟩
  0# + n × c  ∎
×-homo-+ c (suc m) n = begin
  c + (m ℕ+ n) × c     ≈⟨ +-cong refl (×-homo-+ c m n) ⟩
  c + (m × c + n × c)  ≈⟨ sym $ +-assoc c (m × c) (n × c) ⟩
  c + m × c + n × c    ∎

-- _×′_ is homomorphic with respect to _ℕ+_/_+_.

×′-homo-+ : ∀ c m n → (m ℕ+ n) ×′ c ≈ m ×′ c + n ×′ c
×′-homo-+ c m n = begin
  (m ℕ+ n) ×′ c    ≈⟨ sym $ ×≈×′ (m ℕ+ n) c ⟩
  (m ℕ+ n) ×  c    ≈⟨ ×-homo-+ c m n ⟩
  m ×  c + n ×  c  ≈⟨ +-cong (×≈×′ m c) (×≈×′ n c) ⟩
  m ×′ c + n ×′ c  ∎

-- _×_ preserves equality.

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} {n′} {x} {x′} n≡n′ x≈x′ = begin
  n  × x   ≈⟨ reflexive $ PropEq.cong (λ n → n × x) n≡n′ ⟩
  n′ × x   ≈⟨ ×-congʳ n′ x≈x′ ⟩
  n′ × x′  ∎
  where
  ×-congʳ : ∀ n → (_×_ n) Preserves _≈_ ⟶ _≈_
  ×-congʳ 0       x≈x′ = refl
  ×-congʳ (suc n) x≈x′ = x≈x′ ⟨ +-cong ⟩ ×-congʳ n x≈x′

-- _×′_ preserves equality.

×′-cong : _×′_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×′-cong {n} {n′} {x} {x′} n≡n′ x≈x′ = begin
  n  ×′ x   ≈⟨ sym $ ×≈×′ n x ⟩
  n  ×  x   ≈⟨ ×-cong n≡n′ x≈x′ ⟩
  n′ ×  x′  ≈⟨ ×≈×′ n′ x′ ⟩
  n′ ×′ x′  ∎
