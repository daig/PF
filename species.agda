module species where
open import Agda.Primitive renaming (lsuc to ℓs; lzero to ℓz)
import Function
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; subst)
open Eq.≡-Reasoning

module iso where
  _↔_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
  a ↔ b = (a → b) × (b → a)
  re : ∀ {ℓ} {a b : Set ℓ} → a ↔ b → b ↔ a
  re (f , g) = g , f
  id : ∀ {ℓ} {a : Set ℓ} → a ↔ a
  id = Function.id , Function.id
  _⊚_ : ∀ {ℓ} {a b c : Set ℓ} → (b ↔ c) → (a ↔ b) → a ↔ c
  f ⊚ g = (λ z → proj₁ f (proj₁ g z)) , (λ z → snd g (snd f z))
open iso using (_↔_; _⊚_)

open import Function hiding (_↔_)

record Spec ℓ ℓ' : Set (ℓs ℓ ⊔ ℓs ℓ') where -- species
  field
    to : Set ℓ → Set ℓ'
    φ : ∀ {a b} → a ↔ b → to a → to b
--    φι : ∀ a → (φ {a = a}) iso.id ≡ Function.id
--    φ∘ : ∀ a b c →  (f : b ↔ c) (g : a ↔ b) → φ (f ⊚ g) ≡ φ f Function.∘ φ g 

record _↝_ {ℓ ℓf ℓg} (F : Spec ℓ ℓf) (G : Spec ℓ ℓg) : Set (ℓs ℓ ⊔ ℓf ⊔ ℓg) where
  open Spec F renaming (to to F₀; φ to F₁)
  open Spec G renaming (to to G₀; φ to G₁)
  field
    to : ∀ {x} → F₀ x → G₀ x
    -- comm : (x y : Set) (i : x ↔ y) → (to y ∘ F₁ i) ≡ (G₁ i ∘ to x)

Split : ∀ {ℓ} → Set ℓ → Set (ℓs ℓ)
Split {ℓ} x = Σ[ (a , b) ∈ Set ℓ × Set ℓ ] ((a × b) ↔ x)
Partition : ∀ {ℓ} → Set ℓ → Set (ℓs ℓ)
Partition {ℓ} x = Σ[ ind ∈ Set ] Σ[ p ∈ (ind → Set ℓ) ] (Σ[ i ∈ ind ] p i) ↔ x
-- Rectangle : ∀ {ℓ} (x : Set ℓ) → Set (ℓs ℓ)
-- Rectangle x = Σ[ (row , col) ∈ Partition x × Partition x ] 
    



module spec-ops {ℓ ℓ'} (F G : Spec ℓ ℓ') where
  open Spec
  open Spec F renaming (to to F₀; φ to F₁)
  open Spec G renaming (to to G₀; φ to G₁)
  _⊕_ : Spec ℓ ℓ' -- sum
  to _⊕_ x = F₀ x ⊎ G₀ x
  φ _⊕_ i (inj₁ Fa) = inj₁ (F₁ i Fa)
  φ _⊕_ i (inj₂ Ga) = inj₂ (G₁ i Ga)

  _&_ : Spec ℓ ℓ' -- hadamard
  to _&_ x = F₀ x × G₀ x
  φ _&_ i (Fa , Ga) = (F₁ i Fa) , G₁ i Ga

  _⇒_ : Spec ℓ (ℓ ⊔ ℓ')
  to _⇒_ x = (x ↔ x) → F₀ x → G₀ x
  φ _⇒_ a↔b F⇒G  b↔b Fb = G₁ a↔b (F⇒G iso.id (F₁ (iso.re a↔b) (F₁ b↔b Fb)))

  _⊗_ : Spec ℓ (ℓs ℓ ⊔ ℓ')
  to _⊗_ x = Σ[ ((a , b) , _) ∈ Split {ℓ} x ] (F₀ a × G₀ b)
  φ _⊗_ a↔b ((xy , xy↔a) , Fx , Gy) = (xy , (a↔b ⊚ xy↔a)) , Fx , Gy

  _⅋_ : Spec ℓ {!!}
  _⅋_ = {!!}

open spec-ops public
 

module _ where
  open _↝_ 
  tensor-hom : ∀ {ℓ ℓ'} {F G H : Spec ℓ ℓ'} → (F & G) ↝ H → F ↝ (G ⇒ H)
  to (tensor-hom {G = record {φ = G₁}} η) {x} Fx p Gx = to η (Fx , G₁ p Gx)
    
  hom-tensor : ∀ {ℓ ℓ'} {F G H : Spec ℓ ℓ'} → F ↝ (G ⇒ H) → (F & G) ↝ H
  _↝_.to (hom-tensor {F} {G} {H} record { to = η }) (Fx , Gx) = η Fx iso.id Gx

zero top one bot : Spec ℓz ℓz
zero = record { to = λ _ → ⊥     ; φ = λ _ z → z }
top  = record { to = λ _ → ⊤     ; φ = λ _ t → t }
one  = record { to = λ x → x ↔ ⊥ ; φ = λ a↔b a↔⊥ → a↔⊥ ⊚ iso.re a↔b }
bot  = record { to = λ x → x ↔ ⊤ ; φ = λ a↔b a↔⊤ → a↔⊤ ⊚ (iso.re a↔b)}
