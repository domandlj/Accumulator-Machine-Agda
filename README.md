# Semantic Preservation of a Compiler from arithmetic expressions to accumulator machine.

## I. Artihmetic expressions (source language).
### AST
```Agda
Var = ℕ

data Expr : Set where
  const : ℕ   → Expr
  var   : Var → Expr
  plus  : Expr → Expr → Expr
```

### Semantics
```Agda
State = Var → ℕ

source-sem : State → Expr → ℕ
source-sem s (const n) = n
source-sem s (var x) = s x
source-sem s (plus e e') = source-sem s e + source-sem s e'

```

## II. Accumulator machine (target language).
### AST
```Agda
Reg = ℕ

data Ins : Set where
  LI   : ℕ   → Ins
  -- LI n loads a constant n to the accumulator.

  LOAD : Reg → Ins
  -- LOAD r loads register r content into the accumulator.

  STO  : Reg → Ins
  -- STORE r stores accumulator contents into the register r. 

  ADD  : Reg → Ins
  -- ADD r adds to the accumulator the contents of register r.
```

```Agda
data Cell : Set where
  acc : Cell
  reg : Reg → Cell
```


### Semantics
```agda
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
```

## III. Compiler.

```agda
Symt = Var → Reg

compile : Symt → Reg → Expr → List Ins
compile m r (const n) = [ LI n ]
compile m r (var x) = [ LOAD (m x) ]
compile m r (plus e e') = compile m r e ++ [ STO r ] ++ compile m (suc r) e' ++ [ ADD r ]
```

## IV. Semantic Preservation.
```agda
correctness : ∀ e m s s' r →
  (∀ x → m x < r) →
  (∀ x → s x ≡ s' (reg (m x)) ) →
    (sem-code s' (compile m r e) acc ≡ source-sem s e) ×
    ( ∀ x → x < r → sem-code s' (compile m r e) (reg x) ≡ s' (reg x))
```

It's proved in two parts, for the registers that are not the accumulator we use the following invariant
```agda
sem-code-invariant : ∀ m e r r' s → r' < r →
  sem-code s (compile m r e) (reg r') ≡ s (reg r')
```
which states that for a store $s'$ a state $s$ and a register $r', r$ s.t. $r' < r$, when compiling to $r$ the smaller registers remain
unchanged.

This is just proved using the following property multiple times.
```agda
sem-append : ∀ (l₁ l₂ : List Ins) (s : Store) →
  sem-code s (l₁ ++ l₂) ≡ sem-code (sem-code s l₁) l₂
```

```agda
correctness-acc : ∀ e m s s' r →
  (∀ x → m x < r) →
  (∀ x → s x ≡ s' (reg (m x)) ) →

  (sem-code s' (compile m r e) acc ≡ source-sem s e)
```
