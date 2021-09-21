{- 

  This is a variant of the proof given in dialogue.lagda
  (http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.lagda)
  that does not use the formal oracle Ω, and instead directly shows
  the relation between ⟦_⟧ and B⟦_⟧ (see R's definition and main-lemma).
  Then, as before in dialogue-tree-correct, we use generic to consult the
  ``oracle'' α.

  Original author: Martin Escardo.
  Modifications made by Vincent Rahli, 14 March 2015.

-}

module dialogue-without-oracle where

Ķ : ∀{X Y : Set} → X → Y → X
Ķ x y = x
Ş : ∀{X Y Z : Set} → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

_∘_ : ∀{X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

data ℕ : Set where 
  zero : ℕ              
  succ : ℕ → ℕ       
rec : ∀{X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)

data ℕ₂ : Set where
  ₀ ₁ : ℕ₂

data List (X : Set) : Set where
  []        : List X
  _∷_ : X → List X → List X

data Tree (X : Set) : Set where
  empty : Tree X
  branch : X → (ℕ₂ → Tree X) → Tree X

data Σ {X : Set} (Y : X → Set) : Set where
  _,_ : ∀(x : X)(y : Y x) → Σ {X} Y

π₀ : ∀{X : Set} {Y : X → Set} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x
π₁ : ∀{X : Set} {Y : X → Set} → ∀(t : Σ \(x : X) → Y x) → Y(π₀ t)
π₁(x , y) = y

data _≡_ {X : Set} : X → X → Set where
  refl : ∀{x : X} → x ≡ x

sym : ∀{X : Set} → ∀{x y : X} → x ≡ y → y ≡ x
sym refl = refl
trans : ∀{X : Set} → ∀{x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
cong : ∀{X Y : Set} → ∀(f : X → Y) → ∀{x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl
cong₂ : ∀{X Y Z : Set} → ∀(f : X → Y → Z) 
      → ∀{x₀ x₁ : X}{y₀ y₁ : Y} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

data D (X Y Z : Set) : Set where 
  η : Z → D X Y Z
  β : (Y → D X Y Z) → X → D X Y Z

dialogue : ∀{X Y Z : Set} → D X Y Z → (X → Y) → Z
dialogue (η z)   α = z
dialogue (β φ x) α = dialogue (φ(α x)) α

eloquent : ∀{X Y Z : Set} → ((X → Y) → Z) → Set
eloquent f = Σ \d → ∀ α → dialogue d α ≡ f α

Baire : Set
Baire = ℕ → ℕ

B : Set → Set
B = D ℕ ℕ

data _≡[_]_ {X : Set} : (ℕ → X) → List ℕ → (ℕ → X) → Set where
  []  : ∀{α α' : ℕ → X} → α ≡[ [] ] α' 
  _∷_ : ∀{α α' : ℕ → X}{i : ℕ}{s : List ℕ} → α i ≡ α' i → α ≡[ s ] α' → α ≡[ i ∷ s ] α'

continuous : (Baire → ℕ) → Set
continuous f = ∀(α : Baire) → Σ \(s : List ℕ) → ∀(α' : Baire) → α ≡[ s ] α' → f α ≡ f α'

dialogue-continuity : ∀(d : B ℕ) → continuous(dialogue d)
dialogue-continuity (η n) α = ([] , lemma)
  where
    lemma : ∀ α' → α ≡[ [] ] α' → n ≡ n 
    lemma α' r = refl
dialogue-continuity (β φ i) α = ((i ∷ s) , lemma) 
  where
    IH : ∀(i : ℕ) → continuous(dialogue(φ(α i)))
    IH i = dialogue-continuity (φ(α i))
    s : List ℕ
    s = π₀(IH i α)
    claim₀ : ∀(α' : Baire) → α ≡[ s ] α' → dialogue(φ(α i)) α ≡ dialogue(φ(α i)) α'
    claim₀ = π₁(IH i α)
    claim₁ : ∀(α' : Baire) → α i ≡ α' i → dialogue (φ (α i)) α' ≡ dialogue (φ (α' i)) α'
    claim₁ α' r = cong (λ n → dialogue (φ n) α') r
    lemma : ∀(α' : Baire) → α ≡[ i ∷ s ] α'  → dialogue (φ(α i)) α ≡ dialogue(φ (α' i)) α'
    lemma α' (r ∷ rs) = trans (claim₀ α' rs) (claim₁ α' r)

continuity-extensional : ∀(f g : Baire → ℕ) → (∀ α → f α ≡ g α) → continuous f → continuous g
continuity-extensional f g t c α = (π₀(c α) , (λ α' r → trans (sym (t α)) (trans (π₁(c α) α' r) (t α'))))
eloquent-is-continuous : ∀(f : Baire → ℕ) → eloquent f → continuous f
eloquent-is-continuous f (d , e) = continuity-extensional (dialogue d) f e (dialogue-continuity d)

Cantor : Set
Cantor = ℕ → ℕ₂
C : Set → Set
C = D ℕ ℕ₂

data _≡[[_]]_ {X : Set} : (ℕ → X) → Tree ℕ → (ℕ → X) → Set where
  empty : ∀{α α' : ℕ → X} → α ≡[[ empty ]] α' 
  branch : 
    ∀{α α' : ℕ → X}{i : ℕ}{s : ℕ₂ → Tree ℕ} 
    → α i ≡ α' i → (∀(j : ℕ₂) → α ≡[[ s j ]] α') → α ≡[[ branch i s ]] α'

uniformly-continuous : (Cantor → ℕ) → Set
uniformly-continuous f = Σ \(s : Tree ℕ) → ∀(α α' : Cantor) → α ≡[[ s ]] α' → f α ≡ f α'

dialogue-UC : ∀(d : C ℕ) → uniformly-continuous(dialogue d)
dialogue-UC (η n) = (empty , λ α α' n → refl)
dialogue-UC (β φ i) = (branch i s , lemma)
  where
    IH : ∀(j : ℕ₂) → uniformly-continuous(dialogue(φ j))
    IH j = dialogue-UC (φ j)
    s : ℕ₂ → Tree ℕ
    s j = π₀(IH j)
    claim : ∀ j α α' → α ≡[[ s j ]] α' → dialogue (φ j) α ≡ dialogue (φ j) α'
    claim j = π₁(IH j)
    lemma : ∀ α α' → α ≡[[ branch i s ]] α' → dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α' 
    lemma α α' (branch r l) = trans fact₀ fact₁ 
      where
        fact₀ : dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α 
        fact₀ = cong (λ j → dialogue(φ j) α) r
        fact₁ : dialogue (φ (α' i)) α ≡ dialogue (φ (α' i)) α'
        fact₁ = claim (α' i) α α' (l(α' i))

UC-extensional : ∀(f g : Cantor → ℕ) → (∀(α : Cantor) → f α ≡ g α) 
              → uniformly-continuous f → uniformly-continuous g
UC-extensional f g t (u , c) = (u , (λ α α' r → trans (sym (t α)) (trans (c α α' r) (t α'))))

eloquent-is-UC : ∀(f : Cantor → ℕ) → eloquent f → uniformly-continuous f
eloquent-is-UC f (d , e) = UC-extensional (dialogue d) f e (dialogue-UC d)

embed-ℕ₂-ℕ : ℕ₂ → ℕ
embed-ℕ₂-ℕ ₀ = zero
embed-ℕ₂-ℕ ₁ = succ zero

embed-C-B : Cantor → Baire
embed-C-B α = embed-ℕ₂-ℕ ∘ α 
 
C-restriction : (Baire → ℕ) → (Cantor → ℕ)
C-restriction f = f ∘ embed-C-B

prune : B ℕ → C ℕ
prune (η n) = η n
prune (β φ i) = β (λ j → prune(φ(embed-ℕ₂-ℕ j))) i

prune-behaviour : ∀(d : B ℕ)(α : Cantor) → dialogue (prune d) α ≡ C-restriction(dialogue d) α 
prune-behaviour (η n)   α = refl
prune-behaviour (β φ n) α = prune-behaviour (φ(embed-ℕ₂-ℕ(α n))) α

eloquent-restriction : ∀(f : Baire → ℕ) → eloquent f → eloquent(C-restriction f)
eloquent-restriction f (d , c) = (prune d , λ α → trans (prune-behaviour d α) (c (embed-C-B α))) 

data type : Set where
  ι          : type
  _⇒_ : type → type → type

data T : (σ : type) → Set where
  Zero   : T ι
  Succ   : T(ι ⇒ ι)
  Rec  : ∀{σ : type}     → T((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
  K    : ∀{σ τ : type}   → T(σ ⇒ τ ⇒ σ)
  S    : ∀{ρ σ τ : type} → T((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_  : ∀{σ τ : type}   → T(σ ⇒ τ) → T σ → T τ

infixr 1 _⇒_
infixl 1 _·_

Set⟦_⟧ : type → Set
Set⟦ ι ⟧ = ℕ
Set⟦ σ ⇒ τ ⟧ = Set⟦ σ ⟧ → Set⟦ τ ⟧

⟦_⟧ : ∀{σ : type} → T σ → Set⟦ σ ⟧
⟦ Zero ⟧  = zero
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = Ķ
⟦ S ⟧     = Ş
⟦ t · u ⟧   = ⟦ t ⟧ ⟦ u ⟧ 

T-definable : ∀{σ : type} → Set⟦ σ ⟧ → Set
T-definable x = Σ \t → ⟦ t ⟧ ≡ x

kleisli-extension : ∀{X Y : Set} → (X → B Y) → B X → B Y
kleisli-extension f (η x)   = f x
kleisli-extension f (β φ i) = β (λ j → kleisli-extension f (φ j)) i

B-functor : ∀{X Y : Set} → (X → Y) → B X → B Y
B-functor f = kleisli-extension(η ∘ f)

decode-α-is-natural : ∀{X Y : Set}(g : X → Y)(d : B X)(α : Baire) → g(dialogue d α) ≡ dialogue (B-functor g d) α
decode-α-is-natural g (η x)   α = refl
decode-α-is-natural g (β φ i) α = decode-α-is-natural g (φ(α i)) α

decode-kleisli-extension : ∀{X Y : Set}(f : X → B Y)(d : B X)(α : Baire) 
  → dialogue (f(dialogue d α)) α ≡ dialogue (kleisli-extension f d) α
decode-kleisli-extension f (η x)   α = refl
decode-kleisli-extension f (β φ i) α = decode-kleisli-extension f (φ(α i)) α

B-Set⟦_⟧ : type → Set
B-Set⟦ ι ⟧ = B(Set⟦ ι ⟧)
B-Set⟦ σ ⇒ τ ⟧ = B-Set⟦ σ ⟧ → B-Set⟦ τ ⟧

Kleisli-extension : ∀{X : Set} {σ : type} → (X → B-Set⟦ σ ⟧) → B X → B-Set⟦ σ ⟧
Kleisli-extension {X} {ι} = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d 

generic : B ℕ → B ℕ
generic = kleisli-extension(β η)

generic-diagram : ∀(α : Baire)(d : B ℕ) → α(dialogue d α) ≡ dialogue (generic d) α
generic-diagram α (η n) = refl
generic-diagram α (β φ n) = generic-diagram α (φ(α n))

zero' : B ℕ
zero' = η zero
succ' : B ℕ → B ℕ
succ' = B-functor succ

rec' : ∀{σ : type} → (B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → B ℕ → B-Set⟦ σ ⟧
rec' f x = Kleisli-extension(rec f x)

B⟦_⟧ : ∀{σ : type} → T σ → B-Set⟦ σ ⟧
B⟦ Zero ⟧  = zero'
B⟦ Succ ⟧  = succ'
B⟦ Rec ⟧   = rec'
B⟦ K ⟧     = Ķ
B⟦ S ⟧     = Ş
B⟦ t · u ⟧ = B⟦ t ⟧ (B⟦ u ⟧)

dialogue-tree : T((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ t ⟧ generic

R : ∀{σ : type} → Baire → Set⟦ σ ⟧ → B-Set⟦ σ ⟧ → Set

R {ι} α n d = n ≡ dialogue d α

R {σ ⇒ τ} α f f' =
  ∀(x : Set⟦ σ ⟧)(x' : B-Set⟦ σ ⟧) → R {σ} α x x' → R {τ} α (f x) (f' x')

R-kleisli-lemma : ∀(σ : type) (α : Baire) (g : ℕ → Set⟦ σ ⟧)(g' : ℕ → B-Set⟦ σ ⟧)
  → (∀(k : ℕ) → R α (g k) (g' k)) 
  → ∀(n : ℕ)(n' : B ℕ) → R α n n' → R α (g n) (Kleisli-extension g' n')

R-kleisli-lemma ι α g g' rg n n' rn = trans fact₃ (fact₀ α)
  where
    fact₀ : ∀ α → dialogue (g' (dialogue n' α)) α ≡ dialogue (kleisli-extension g' n') α
    fact₀ = decode-kleisli-extension g' n'
    fact₁ : g n ≡ dialogue (g' n) α
    fact₁ = rg n
    fact₂ : dialogue (g' n) α ≡ dialogue (g' (dialogue n' α)) α
    fact₂ = cong (λ k → dialogue (g' k) α) rn
    fact₃ : g n ≡ dialogue (g' (dialogue n' α)) α
    fact₃ = trans fact₁ fact₂

R-kleisli-lemma (σ ⇒ τ) α g g' rg n n' rn 
  = λ y y' ry → R-kleisli-lemma τ α (λ k → g k y) (λ k → g' k y') (λ k → rg k y y' ry) n n' rn 

main-lemma : ∀{σ : type}(t : T σ) (α : Baire) → R α ⟦ t ⟧ (B⟦ t ⟧)

main-lemma Zero = λ α → refl
main-lemma Succ = lemma
  where 
    claim : ∀ α n n' → n ≡ dialogue n' α → succ n ≡ succ(dialogue n' α)
    claim α n n' s = cong succ s  
    lemma : ∀(α : Baire) (n : ℕ)(n' : B ℕ) → (n ≡ dialogue n' α)
          → succ n ≡ dialogue (B-functor succ n') α
    lemma α n n' rn = trans (claim α n n' rn) (decode-α-is-natural succ n' α)

main-lemma {(σ ⇒ .σ) ⇒ .σ ⇒ ι ⇒ .σ} Rec = lemma
  where
    lemma : ∀ (α : Baire) (f : Set⟦ σ ⟧ → Set⟦ σ ⟧)(f' : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → R {σ ⇒ σ} α f f' 
      → ∀(x : Set⟦ σ ⟧)(x' : B-Set⟦ σ ⟧) 
      → R {σ} α x x' → ∀(n : ℕ)(n' : B ℕ) → R {ι} α n n'
      → R {σ} α (rec f x n) (Kleisli-extension(rec f' x') n')
    lemma α f f' rf x x' rx = R-kleisli-lemma σ α g g' rg
      where
        g : ℕ → Set⟦ σ ⟧
        g k = rec f x k
        g' : ℕ → B-Set⟦ σ ⟧
        g' k = rec f' x' k
        rg : ∀(k : ℕ) → R α (g k) (g' k)
        rg zero = rx  
        rg (succ k) = rf (g k) (g' k) (rg k)

main-lemma K = λ α x x' rx y y' ry → rx 

main-lemma S = λ α f f' rf g g' rg x x' rx → rf x x' rx (g x) (g' x') (rg x x' rx) 

main-lemma (t · u) = λ α → main-lemma t α ⟦ u ⟧ B⟦ u ⟧ (main-lemma u α)

dialogue-tree-correct : ∀(t : T((ι ⇒ ι) ⇒ ι))(α : Baire) → ⟦ t ⟧ α ≡ dialogue (dialogue-tree t) α
dialogue-tree-correct t α = claim₁
  where
    lemma : ∀(n : ℕ)(n' : B ℕ) → n ≡ dialogue n' α → α n ≡ dialogue (generic n') α
    lemma n n' rn = trans (cong α rn) (generic-diagram α n') 
    claim₁ : ⟦ t ⟧ α ≡ dialogue (dialogue-tree t) α
    claim₁ = main-lemma t α α generic lemma

eloquence-theorem : ∀(f : Baire → ℕ) → T-definable f → eloquent f
eloquence-theorem f (t , r) = (dialogue-tree t , λ α → trans(sym(dialogue-tree-correct t α))(cong(λ g → g α) r))

corollary₀ : ∀(f : Baire → ℕ) → T-definable f → continuous f
corollary₀ f d = eloquent-is-continuous f (eloquence-theorem f d)

corollary₁ : ∀(f : Baire → ℕ) → T-definable f → uniformly-continuous(C-restriction f) 
corollary₁ f d = eloquent-is-UC (C-restriction f) (eloquent-restriction f (eloquence-theorem f d))
