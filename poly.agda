module poly where
open import Function
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)



module arena where
  record Arena : Set₁ where
    constructor _◅_
    field
        shape : Set
        pos : shape → Set
  open Arena public
  module _ (a : Arena) where
    open Arena a renaming (shape to A⁺; pos to A⁻)
    Display : Set
    Display = Σ A⁺ A⁻
    _⦅_⦆ : Set → Set
    _⦅_⦆ y = Σ A⁺ \ a → (A⁻ a → y) 
    -- a ⦅ ⊤ ⦆ ≡ A⁺
open arena public


module lens where
    record _↝_ (a b : Arena) : Set where
      constructor _⇵_
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)
      field
        get : A⁺ → B⁺
        set : (sh : A⁺) → B⁻ (get sh) → A⁻ sh
    open _↝_ public
    idLens : (a : Arena) → a ↝ a
    get (idLens a) x = x
    set (idLens a) _ x = x
    _▸_ : ∀ {a b c} → (a ↝ b) → (b ↝ c) → (a ↝ c)
    get (l1 ▸ l2) = λ x → get l2 (get l1 x)
    set (l1 ▸ l2) = λ shₐ x → set l1 shₐ (set l2 (get l1 shₐ) x)

    module _ {a c : Arena} (l : a ↝ c) where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena c renaming (shape to C⁺; pos to C⁻)
      open _↝_ l renaming (get to f; set to f†)
      Factor : Σ[ b ∈ Arena ] (a ↝ b) × (b ↝ c)
      Factor = b , (vertf , cartf) where
        b : Arena
        shape b = A⁺; pos b = C⁻ ∘ f
        vertf : a ↝ b
        get vertf = id; set vertf = f†
        cartf : b ↝ c
        get cartf = f; set cartf _shₐ x = x
open lens

module arenas where
    _◄_ : (i o : Set) → Arena
    o ◄ i = o ◅ (λ _ → i)

    Self : Set → Arena
    Self s = s ◄ s
    Closed : Arena
    Closed = ⊤ ◄ ⊤

    module reflections (t : Set) where
        Exception Emitter Sensor : Arena
        Exception = t ◄ ⊥
        Emitter   = t ◄ ⊤
        Sensor    = ⊤ ◄ t
    open reflections public
    module ev (a : Arena) where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      ev0 ev1 ev1y : Arena
      ev0 = Exception $ a ⦅ ⊥ ⦆
      fromEv0 : ev0 ↝ a
      fromEv0 = record { get = fst ; set = snd }
      ev1 = Exception A⁺ -- (a ⦅ ⊤ ⦆)
      toEv1 : a ↝ ev1
      toEv1 = record { get = id ; set = λ _shₐ → ⊥-elim }

      ev1y = Emitter A⁺
      fromEv1y : ev1y ↝ a
      fromEv1y = id ⇵ (λ _ _ → tt)
    open ev public
open arenas public
module lenses {a b : Set} (f : a → b) where
  constant : Exception a ↝ Exception b
  constant = f ⇵ λ _ p → p
  emitter : Emitter a ↝ Emitter b
  emitter = f ⇵ λ _ (.tt) → tt
  sensor : Sensor b ↝ Sensor a
  sensor = (λ (.tt) → tt) ⇵ λ _sh → f
  enclose : (a ◄ b) ↝ Closed
  enclose = (λ _ → tt) ⇵ λ sh (.tt) → f sh
open lenses public
auto : {m : Set} → Emitter m ↝ Closed
auto {m} = enclose \ _ → tt

module functors (f : Set → Set) where
    record Functor : Set₁ where
      field φ : ∀ {a b} → (a → b) → f a → f b
    open Functor ⦃...⦄
    record Monad : Set₁ where
      field
        ⦃ Functor⇒Monad ⦄ : Functor
        η : ∀ {a} → a → f a
        μ : ∀ {a} → f (f a) → f a
    open Monad ⦃...⦄

  
    module _ ⦃ f_functor : Functor ⦄ where
      lift : Arena → Arena
      lift a = A⁺ ◅ (f ∘ A⁻) where
          open Arena a renaming (shape to A⁺; pos to A⁻)
      liftLens : ∀ {a b} → a ↝ b → lift a ↝ lift b
      liftLens l = l .get ⇵ (φ ∘ l .set)


    module lift_comonad {a : Arena} ⦃ f_monad : Monad ⦄ where
      extract : lift a ↝ a
      extract = id ⇵ λ _ → η
      duplicate : lift a ↝ lift (lift a)
      duplicate = id ⇵ λ _ → μ

module list where
  Vect : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
  Vect n t = Fin n → t
  List : ∀ {ℓ} → Set ℓ → Set ℓ
  List t = Σ[ n ∈ ℕ ] Vect n t
  len : ∀ {ℓ} {a : Set ℓ} → List a → ℕ
  len = fst
  head : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ Nat.zero) → a
  head (Nat.zero , as) n≢0 = ⊥-elim (n≢0 refl)
  head (Nat.suc n , as) _ = as Fin.zero
  tail : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ Nat.zero) → List a
  tail (Nat.zero , as) n≢0 = ⊥-elim (n≢0 refl)
  tail (Nat.suc n , as) _ = n , (as ∘ Fin.inject₁)
open list public
  
  

module ops where
  module sum where
    zero : Arena
    zero = ⊥ ◄ ⊥
    _⊕_ : Arena → Arena → Arena
    a ⊕ b = (A⁺ ⊎ B⁺) ◅ (λ{(inj₁ a⁺) → A⁻ a⁺; (inj₂ b⁺) → B⁻ b⁺}) where
        open Arena a renaming (shape to A⁺; pos to A⁻)
        open Arena b renaming (shape to B⁺; pos to B⁻)
    sum : (Σ[ ind ∈ Set ] (ind → Arena)) → Arena
    sum (ind , arena) = (Σ[ i ∈ ind ] shape (arena i)) ◅ λ (i , sh) → pos (arena i) sh
    _⟦⊕⟧_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊕ x) ↝ (b ⊕ y)
    _⟦⊕⟧_ {a} {b} {x} {y} a↝b x↝y  = g ⇵ s where
        open Arena a renaming (shape to A⁺; pos to A⁻)
        open Arena b renaming (shape to B⁺; pos to B⁻)
        open Arena x renaming (shape to X⁺; pos to X⁻)
        open Arena y renaming (shape to Y⁺; pos to Y⁻)
        g : A⁺ ⊎ X⁺ → B⁺ ⊎ Y⁺
        g (inj₁ a⁺) = inj₁ (get a↝b a⁺)
        g (inj₂ x⁺) = inj₂ (get x↝y x⁺)
        s : (sh : A⁺ ⊎ X⁺) → pos (b ⊕ y) (g sh) → pos (a ⊕ x) sh
        s (inj₁ a⁺) b⁻ = set a↝b a⁺ b⁻
        s (inj₂ x⁺) y⁻ = set x↝y x⁺ y⁻
    copair : ∀ {a b x} → a ↝ x → b ↝ x → (a ⊕ b) ↝ x
    copair {a} {b} {x} a↝x b↝x = g ⇵ s where
        open Arena a renaming (shape to A⁺; pos to A⁻)
        open Arena b renaming (shape to B⁺; pos to B⁻)
        open Arena x renaming (shape to X⁺; pos to X⁻)
        g : A⁺ ⊎ B⁺ → X⁺
        g (inj₁ a) = get a↝x a
        g (inj₂ b) = get b↝x b
        s : (sh : A⁺ ⊎ B⁺) → X⁻ (g sh) → pos (a ⊕ b) sh
        s (inj₁ a) x = set a↝x a x
        s (inj₂ b) x = set b↝x b x
  module product where
    one = ⊥ ◄ ⊤
    _⊗_ : Arena → Arena → Arena
    a ⊗ b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) → A⁻ a⁺ ⊎ B⁻ b⁺ where
        open Arena a renaming (shape to A⁺; pos to A⁻)
        open Arena b renaming (shape to B⁺; pos to B⁻)

    {-# TERMINATING #-}
    prodList : List Arena → Arena
    prodList (Nat.zero , _) = one
    prodList as@(Nat.suc n , _) = head as (λ()) ⊗ prodList (tail as (λ())) 

    _⟦⊗⟧_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊗ x) ↝ (b ⊗ y)
    _⟦⊗⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)
      open Arena x renaming (shape to X⁺; pos to X⁻)
      open Arena y renaming (shape to Y⁺; pos to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (get a↝b a⁺) , (get x↝y x⁺)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (get a↝b a⁺) ⊎ Y⁻ (get x↝y x⁺) → A⁻ a⁺ ⊎ X⁻ x⁺
      s (a⁺ , x⁺) (inj₁ b⁻) = inj₁ (set a↝b a⁺ b⁻)
      s (a⁺ , x⁺) (inj₂ y⁻) = inj₂ (set x↝y x⁺ y⁻)
    
    prod : Σ[ ind ∈ Set ] (ind → Arena) → Arena
    prod (ind , arena) = ((i : ind) → shape (arena i))
                       ◅ (λ sh → Σ[ i ∈ ind ] pos (arena i) (sh i))

    pair : ∀ {x a b} → x ↝ a → x ↝ b → x ↝ (a ⊗ b)
    pair {x} {a} {b} x↝a x↝b = g ⇵ {!s!} where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)
      open Arena x renaming (shape to X⁺; pos to X⁻)
      g : X⁺ → A⁺ × B⁺
      g x⁺ = get x↝a x⁺ , get x↝b x⁺
      s : (x⁺ : X⁺) → pos (a ⊗ b) (g x⁺) → X⁻ x⁺
      s x⁺ (inj₁ a⁻) = set x↝a x⁺ a⁻
      s x⁺ (inj₂ b⁻) = set x↝b x⁺ b⁻

  module juxtaposition where
    _&_ : Arena → Arena → Arena
    a & b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) →  A⁻ a⁺ × B⁻ b⁺ where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)

    {-# TERMINATING #-}
    juxtList : List Arena → Arena
    juxtList (Nat.zero , _) = Closed -- ⊤ ◄ ⊤
    juxtList as@(Nat.suc n , _) = head as (λ ()) & juxtList (tail as (λ ()))

    juxtLens : ∀ {a b x y} → a ↝ b → x ↝ y → (a & x) ↝ (b & y)
    juxtLens {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)
      open Arena x renaming (shape to X⁺; pos to X⁻)
      open Arena y renaming (shape to Y⁺; pos to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (get a↝b a⁺) , (get x↝y x⁺)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (get a↝b a⁺) × Y⁻ (get x↝y x⁺) → A⁻ a⁺ × X⁻ x⁺
      s (a⁺ , x⁺) (b⁻ , y⁻) = set a↝b a⁺ b⁻ , set x↝y x⁺ y⁻

  module compose where
    _⊚_ : Arena → Arena → Arena
    a ⊚ b = (Σ[ a⁺ ∈ A⁺ ] (A⁻ a⁺ → B⁺))
          ◅ λ (a⁺ , bs) → Σ[ a⁻ ∈ A⁻ a⁺ ] (B⁻ $ bs a⁻) where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)

    _⟦⊚⟧_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊚ x) ↝ (b ⊚ y)
    _⟦⊚⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (shape to A⁺; pos to A⁻)
      open Arena b renaming (shape to B⁺; pos to B⁻)
      open Arena x renaming (shape to X⁺; pos to X⁻)
      open Arena y renaming (shape to Y⁺; pos to Y⁻)
      g : (Σ[ a⁺ ∈ A⁺ ] (A⁻ a⁺ → X⁺)) → (Σ[ b⁺ ∈ B⁺ ] (B⁻ b⁺ → Y⁺))
      g (a⁺ , xs) = get a↝b a⁺ , get x↝y ∘ xs ∘ set a↝b a⁺
      s : ((a⁺ , xs) : (Σ[ a⁺ ∈ A⁺ ] (A⁻ a⁺ → X⁺)))
        → Σ[ b⁻ ∈ B⁻ (get a↝b a⁺) ] (Y⁻ ∘ get x↝y ∘ xs $ set a↝b a⁺ b⁻)
        → Σ[ a⁻ ∈ A⁻ a⁺ ] (X⁻ $ xs a⁻)
      s (a⁺ , xs) (b⁻ , y⁻) =  a⁻ , set x↝y (xs a⁻) y⁻ where
         a⁻ = set a↝b a⁺ b⁻

    _ᵒ_ : Arena → ℕ → Arena
    _ ᵒ Nat.zero = Closed
    a ᵒ Nat.suc n = a ⊚ (a ᵒ n)

    
    _⟦ᵒ⟧_ : {a b : Arena} → a ↝ b → (n : ℕ) → (a ᵒ n) ↝ (b ᵒ n)
    _  ⟦ᵒ⟧ Nat.zero    = idLens Closed 
    lens ⟦ᵒ⟧ Nat.suc n = lens ⟦⊚⟧ (lens ⟦ᵒ⟧ n)

    EmitterPow : (a : Set) (n : ℕ) → (Emitter a ᵒ n) ↝ Emitter (Vect n a)
    EmitterPow a Nat.zero = (λ _ ()) ⇵ (λ sh _ → tt)
    EmitterPow a (Nat.suc n) = {!!} ⇵ {!!}
