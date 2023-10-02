module AccMachine where
open import Data.Nat
open import Data.List
open import Relation.Nullary
open import Relation.Binary using (Decidable)
open import Data.Bool using (true ; false)
open import Data.Nat.Properties using (<⇒≤ ; <⇒≢ ; +-comm ; ≤-refl  )
open import Data.Empty
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_ ; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


{-

  I. Source Language: Arithmetic Expressions.

-}

-- AST.
Var = ℕ

data Expr : Set where
  const : ℕ   → Expr
  var   : Var → Expr
  plus  : Expr → Expr → Expr



-- Semantics.
State = Var → ℕ

source-sem : State → Expr → ℕ
source-sem s (const n) = n
source-sem s (var x) = s x
source-sem s (plus e e') = source-sem s e + source-sem s e'


{-

  II. Target Language: Register Machine.

-}

-- AST.
Reg = ℕ
Mem = ℕ

data Ins : Set where
  LI   : ℕ   → Ins
  LOAD : Reg → Ins
  STO  : Reg → Ins
  ADD  : Reg → Ins

data Cell : Set where
  acc : Cell
  reg : Reg → Cell



reg-inj : ∀ {x y} → reg x ≡ reg y → x ≡ y
reg-inj {x} {.x} refl = refl

_≟Cell_ : Decidable {A = Cell} _≡_
acc ≟Cell acc = yes refl
acc ≟Cell reg _ = no (λ ())
reg _ ≟Cell acc = no (λ ())
reg x ≟Cell reg y with x ≟ y
... | yes x≡y = yes (cong reg x≡y)
... | no x≢y = no diff-var
  where
    diff-var : ¬ reg x ≡ reg y
    diff-var x≡y = contradiction (reg-inj x≡y)  x≢y


-- Semantics.
Store = Cell → ℕ

update : Store → Cell → ℕ → Store
update s c v c' with c ≟Cell c'
... | yes _ = v
... | no _  = s c'



sem-ins : Store → Ins → Store
sem-ins s (LI n) = update s acc n
sem-ins s (LOAD r) = update s acc (s (reg r))
sem-ins s (STO r) = update s (reg r) (s acc)
sem-ins s (ADD r) = update s acc (s acc + s (reg r))


sem-code : Store → List Ins → Store
sem-code s [] = s
sem-code s (i ∷ li) = sem-code (sem-ins s i) li



{-

  III. Compiler.

-}

Symt = Var → Reg

compile : Symt → Reg → Expr → List Ins
compile m r (const n) = [ LI n ]
compile m r (var x) = [ LOAD (m x) ]
compile m r (plus e e') = compile m r e ++ [ STO r ] ++ compile m (suc r) e' ++ [ ADD r ]



{-

  IV. Semantic Preservation of Compiler.

-}


update-prop : ∀ c c' s v (p : c ≢ c') → (update s c v) c' ≡ s c'
update-prop c c' s v c≢c' with c ≟Cell c'
... | yes c≡c'  = ⊥-elim (contradiction c≡c' c≢c')
... | no _ = refl

update-c≡c' : ∀ c c' s v (p : c ≡ c') → (update s c v) c' ≡ v
update-c≡c' c c' s v c≡c' with c ≟Cell c'
... | no c≢c'  = ⊥-elim (contradiction c≡c' c≢c')
... | yes _ = refl

store-prop : ∀ r r' → r ≢ r' → reg r ≢ reg r'
store-prop r r' r≢r'  regr≡regr' =  contradiction r≡r' r≢r'
  where
    r≡r' = reg-inj regr≡regr'



++-dist : ∀ {A : Set} x (l₁ l₂ : List A) →
  (x ∷ l₁) ++ l₂ ≡  x ∷ (l₁ ++ l₂)
++-dist x [] l₂ = refl
++-dist x (x₁ ∷ l₁) l₂
  rewrite ++-dist x l₁ l₂ = refl


sem-append : ∀ (l₁ l₂ : List Ins) (s : Store) →
  sem-code s (l₁ ++ l₂) ≡ sem-code (sem-code s l₁) l₂

sem-append [] l₂ s = refl
sem-append (x ∷ l₁) l₂ s =
  begin
    sem-code s ( (x ∷ l₁) ++ l₂ )
  ≡⟨ cong (λ z → sem-code s z) (++-dist x l₁ l₂) ⟩
    sem-code s ( x ∷ (l₁ ++ l₂) )
  ≡⟨⟩
      sem-code (sem-ins s x) (l₁ ++ l₂)
  ≡⟨ sem-append l₁ l₂ (sem-ins s x) ⟩
    sem-code (sem-code (sem-ins s x) l₁) l₂
  ≡⟨⟩
    sem-code (sem-code s (x ∷ l₁)) l₂
  ∎


sem-code-invariant : ∀ m e r r' s → r' < r →
  sem-code s (compile m r e) (reg r') ≡ s (reg r')

sem-code-invariant _ (const _) _ _ _ _ = refl
sem-code-invariant _ (var _) _ _ _ _ = refl
sem-code-invariant m (plus e e') r r' s r'<r =
  begin
    sem-code s (compile m r (plus e e')) (reg r')
  ≡⟨⟩
    sem-code s ( compile m r e ++ ([ STO r ] ++ compile m (suc r) e' ++ [ ADD r ]) ) (reg r')
  ≡⟨ cong (λ z →  z (reg r'))
      (sem-append (compile m r e) ([ STO r ] ++ compile m (suc r) e' ++ [ ADD r ]) s)  ⟩
     sem-code (sem-code s (compile m r e)) ([ STO r ] ++ (compile m (suc r) e' ++ [ ADD r ])) (reg r')
  ≡⟨ cong (λ z → z (reg r'))
      (sem-append [ STO r ] ( compile m (suc r) e' ++ [ ADD r ]) (sem-code s (compile m r e))) ⟩
     sem-code (sem-code (sem-code s (compile m r e)) [ STO r ]) (compile m (suc r) e' ++ [ ADD r ]) (reg r')
  ≡⟨ cong (λ z → z (reg r'))
      (sem-append (compile m (suc r) e') [ ADD r ] (sem-code (sem-code s (compile m r e)) [ STO r ])) ⟩
     sem-code (sem-code ( (sem-code (sem-code s (compile m r e)) [ STO r ])) (compile m (suc r) e')) [ ADD r ] (reg r')
  ≡⟨⟩
    sem-code s' [ ADD r ] (reg r')
  ≡⟨⟩
    (update s' acc (s' acc + s' (reg r))) (reg r')
  ≡⟨ update-prop acc (reg r') s' ((s' acc + s' (reg r))) acc≢regr' ⟩
    s' (reg r')
  ≡⟨ ih2 ⟩
     (update s'' (reg r) (s'' acc)) (reg r')
  ≡⟨ update-prop (reg r) (reg r') s'' (s'' acc) (store-prop r r' (Eq.≢-sym r'≢r)) ⟩
   s'' (reg r')
  ≡⟨ ih ⟩
     s (reg r')
  ∎
  where
    r'≢r : r' ≢ r
    r'≢r = <⇒≢ r'<r

    acc≢regr' : acc ≢ reg r'
    acc≢regr' = λ ()

    s'' = sem-code s (compile m r e)

    ih : s'' (reg r') ≡ s (reg r')
    ih = sem-code-invariant m e r r' s r'<r

    r'≤r : r' ≤ r
    r'≤r = <⇒≤ r'<r

    s' = sem-code (update s'' (reg r) (s'' acc)) (compile m (suc r) e')

    ih2 : s' (reg r') ≡ (update s'' (reg r) (s'' acc)) (reg r')
    ih2 = sem-code-invariant m e' (suc r) r' (update s'' (reg r) (s'' acc)) (s≤s (r'≤r))




correctness-reg : ∀ e m (s : State) (s' : Store) r →
  (∀ (v : ℕ) → m v < r) →
  (∀ (v : ℕ) → (s v) ≡ s' (reg (m v)) ) →
    (( ∀ x → x < r → sem-code s' (compile m r e) (reg x) ≡ s' (reg x)))

correctness-reg (const n) m s s' r mv<r sv≡s'regmv x x<r = refl
correctness-reg (var y) m s s' r mv<r sv≡s'regmv x x<r = refl
correctness-reg (plus e₁ e₂) m s s' r mv<r sv≡s'regmv x x<r =
  sem-code-invariant m (plus e₁ e₂) r x s' x<r


correctness-acc : ∀ e m s s' r →
  (∀ x → m x < r) →
  (∀ x → s x ≡ s' (reg (m x)) ) →

  (sem-code s' (compile m r e) acc ≡ source-sem s e)

correctness-acc (const n) m s s' r mv<r sv≡s'regmv = refl
correctness-acc (var x) m s s' r mv<r sv≡s'regmv =
  begin
    update s' acc (s' (reg (m x))) acc
  ≡⟨ cong (λ z → update s' acc z acc) (sym (sv≡s'regmv x)) ⟩
    update s' acc (s x) acc
  ≡⟨⟩
    s x
  ∎
correctness-acc (plus e₁ e₂) m s s' r mv<r sx≡s'regmx =
  begin
     sem-code s' (compile m r e₁ ++ ([ STO r ] ++  compile m (suc r) e₂ ++ [ ADD r ])) acc
  ≡⟨ cong (λ z → z acc)
    (sem-append (compile m r e₁) (([ STO r ] ++ compile m (suc r) e₂ ++ [ ADD r ])) s') ⟩
    sem-code (sem-code s' (compile m r e₁)) ([ STO r ] ++ (compile m (suc r) e₂ ++ [ ADD r ])) acc
  ≡⟨ cong (λ z → z acc)
    (sem-append [ STO r ] (compile m (suc r) e₂ ++ [ ADD r ]) (sem-code s' (compile m r e₁))) ⟩
    sem-code (sem-code (sem-code s' (compile m r e₁)) [ STO r ]) (compile m (suc r) e₂ ++ [ ADD r ]) acc
  ≡⟨ cong (λ z → z acc)
    (sem-append (compile m (suc r) e₂) [ ADD r ] (sem-code (sem-code s' (compile m r e₁)) [ STO r ])) ⟩
    (sem-code (sem-code (sem-code (sem-code s' (compile m r e₁)) [ STO r ])
      (compile m (suc r) e₂)) [ ADD r ]) acc
  ≡⟨⟩
    update
      (sem-code
       (update (sem-code s' (compile m r e₁)) (reg r)
        (sem-code s' (compile m r e₁) acc))
       (compile m (suc r) e₂)) acc  (t1 + t2) acc
  ≡⟨ update-c≡c' acc acc ( (sem-code
       (update (sem-code s' (compile m r e₁)) (reg r)
       (sem-code s' (compile m r e₁) acc)) (compile m (suc r) e₂))) (t1 + t2) refl ⟩
    t1 + t2
  ≡⟨ cong (λ z → z + t2) t1≡t1' ⟩
    t1' + t2
  ≡⟨ cong (λ z → t1' + z) t2≡t2' ⟩
    t1' + t2'
  ≡⟨ cong (λ z → z + t2') t1'≡source-sem ⟩
    source-sem s e₂ + t2'
  ≡⟨ cong (λ z → (source-sem s e₂) + z) t2'≡source-sem ⟩
    source-sem s e₂ + source-sem s e₁
  ≡⟨ +-comm (source-sem s e₂) (source-sem s e₁) ⟩
   source-sem s e₁ + source-sem s e₂
  ∎
  where
    h1 = correctness-acc e₁ m s s' r mv<r sx≡s'regmx
    t1 : ℕ
    t1 =  sem-code (update (sem-code s' (compile m r e₁)) (reg r)
      (sem-code s' (compile m r e₁) acc)) (compile m (suc r) e₂) acc

    t1' = sem-code (update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) )
      (compile m (suc r) e₂) acc

    t1≡t1' : t1 ≡ t1'
    t1≡t1' = cong (λ z →  sem-code (update (sem-code s' (compile m r e₁)) (reg r) (z) )
      (compile m (suc r) e₂) acc) h1

    mx<sucr : ∀ x → m x < suc r
    mx<sucr x = s≤s (<⇒≤ (mv<r x))

    baz : (x : Var) → reg r ≢ reg (m x) →
      update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x)) ≡
      (sem-code s' (compile m r e₁)) (reg (m x))
    baz x r≢mx = update-prop (reg r) (reg (m x)) (sem-code s' (compile m r e₁)) (source-sem s e₁)  r≢mx

    baz2 : ∀ x → (sem-code s' (compile m r e₁)) (reg (m x)) ≡ s' (reg (m x))
    baz2 x = correctness-reg e₁ m s s' r (mv<r) (sx≡s'regmx) ((m x)) (mv<r x)


    mx≢r : ∀ x → m x ≢ r
    mx≢r x = <⇒≢ (mv<r x)

    regmx≢regr : ∀ x → reg (m x) ≢ reg r
    regmx≢regr x regmx≡regr = contradiction (reg-inj regmx≡regr) (mx≢r x)

    baz3 : (x : Var) → update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x)) ≡ s x
    baz3 x =
      begin
        update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x))
      ≡⟨ baz x (Eq.≢-sym (regmx≢regr x) ) ⟩
          (sem-code s' (compile m r e₁)) (reg (m x))
      ≡⟨ baz2 x ⟩
        s' (reg (m x))
      ≡⟨ sym (sx≡s'regmx x) ⟩
        s x
      ∎

    t1'≡source-sem : t1' ≡ source-sem s e₂
    t1'≡source-sem =
      begin
        sem-code (update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁)) (compile m (suc r) e₂) acc
      ≡⟨ correctness-acc e₂ m s (update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁)) (suc r) mx<sucr
         (λ x → sym (baz3 x))  ⟩
        source-sem s e₂
      ∎


    t2 : ℕ
    t2 =   sem-code
       (update (sem-code s' (compile m r e₁)) (reg r)
        (sem-code s' (compile m r e₁) acc))
       (compile m (suc r) e₂) (reg r)


    t2' = sem-code (update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) ) (compile m (suc r) e₂) (reg r)


    t2≡t2' : t2 ≡ t2'
    t2≡t2' = cong (λ z →  sem-code (update (sem-code s' (compile m r e₁)) (reg r) (z) )
      (compile m (suc r) e₂) (reg r)) h1

    lem : (x : ℕ) → update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x)) ≡
      (sem-code s' (compile m r e₁)) (reg (m x))
    lem x = update-prop (reg r) (reg (m x)) (sem-code s' (compile m r e₁)) (source-sem s e₁) (Eq.≢-sym ( regmx≢regr x))

    lem2 : ∀ x → (sem-code s' (compile m r e₁)) (reg (m x)) ≡ s' (reg (m x))
    lem2 x = correctness-reg e₁ m s s' r mv<r sx≡s'regmx (m x) (mv<r x)


    teo : (x : ℕ) → update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x)) ≡ s x
    teo x = 
      begin
         update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg (m x))
      ≡⟨ lem x ⟩
         (sem-code s' (compile m r e₁)) (reg (m x))
      ≡⟨ lem2 x ⟩
        s' (reg (m x))
      ≡⟨ sym (sx≡s'regmx x) ⟩
        s x
      ∎

    teo' : t2' ≡ update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg r)
    teo' = correctness-reg e₂ m s ((update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) ))
      (suc r) mx<sucr (λ z → sym (teo z)) r (s≤s (≤-refl))

    teo'' : update (sem-code s' (compile m r e₁)) (reg r) (source-sem s e₁) (reg r) ≡ source-sem s e₁
    teo'' = update-c≡c' (reg r) (reg r) (sem-code s' (compile m r e₁)) (source-sem s e₁) refl

    t2'≡source-sem : t2' ≡ source-sem s e₁
    t2'≡source-sem = trans teo' teo''


correctness : ∀ e m s s' r →
  (∀ x → m x < r) →
  (∀ x → s x ≡ s' (reg (m x)) ) →
    (sem-code s' (compile m r e) acc ≡ source-sem s e) ×
    ( ∀ x → x < r → sem-code s' (compile m r e) (reg x) ≡ s' (reg x))

correctness e m s s' r p p' =
  correctness-acc e m s s' r p p' ,
  correctness-reg e m s s' r p p'
