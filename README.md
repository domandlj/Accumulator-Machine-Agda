# Semantic Preservation of a Compiler from Arithmetic Expressions to Accumulator Machine.

This is a proof of semantic preservation of a compiler of arithmetic expressions to a register machine as the one in  
"Correctness of a compiler for arithmetic expressions" (McCarthy and Painter 1967). The formalization is in Agda.   
The proof is not as in the paper but just using pattern matching, induction and equational reasoning.

## I. Artihmetic expressions (source language).
The source language is just natural number arithemtic expressions with additon.

### AST
```Agda
Var = ℕ

data Expr : Set where
  const : ℕ   → Expr
  var   : Var → Expr
  plus  : Expr → Expr → Expr
```

The semantics are straightforward.
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


The memory cells are just a special purpouse register $acc$ (the accumulator) and infinite countable registers $reg \ 0, reg \ 1, reg \ 2,...$
```Agda
data Cell : Set where
  acc : Cell
  reg : Reg → Cell
```


### Semantics
The memory model is just a map from memory cells to natural numbers.
```agda
Store = Cell → ℕ

update : Store → Cell → ℕ → Store
update s c v c' with c ≟Cell c'
... | yes _ = v
... | no _  = s c'
```
We use $update \ s \ c \ v$ to update the contents of cell $c$ with value $v$. We use $≟Cell$ to decide if two cells are  
equal, they are equall if they have the same register number.


The semantics of each instruction is just an update of the store.
```agda
sem-ins : Store → Ins → Store
sem-ins s (LI n) = update s acc n
sem-ins s (LOAD r) = update s acc (s (reg r))
sem-ins s (STO r) = update s (reg r) (s acc)
sem-ins s (ADD r) = update s acc (s acc + s (reg r))
```

A list of instructions is a program, and it's semantics are just succesive modifications of the store for each instruction.
```agda
sem-code : Store → List Ins → Store
sem-code s [] = s
sem-code s (i ∷ li) = sem-code (sem-ins s i) li
```

## III. Compiler.
The variables of the target language needs to be assigned to the registers of the register machinge, we use the following symbol
table as just maps from variables to registers and there is no problem since both are infinite many.
```agda
Symt = Var → Reg
```

Given a symbol table $w$, we compile an expression $e$ using the registers greater or equall $r$
```agda
compile : Symt → Reg → Expr → List Ins
compile m r (const n) = [ LI n ]
compile m r (var x) = [ LOAD (m x) ]
compile m r (plus e e') = compile m r e ++ [ STO r ] ++ compile m (suc r) e' ++ [ ADD r ]
```

## IV. Semantic Preservation.
We have as premises that for all state $s$, store $s'$, variables $x$, registers $r$ and symbol table $m$ 
* $m \ x < r$
* $s \ x ≡ s' \ (reg (m \ x))$, i.e., the state has the same contents as the store.

And with that one can conclude that 
* The contents of the accumulator in the store are the same as the ones of the semantic of the  
compiled expression with the state.  
* All registers less than $r$ remain unchanged on the store after compiling.

Formally,
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

We use the first the properties of the registers to prove that the contents of the accumulator in the store are the same as the ones  
of the semantic of the compiled expression with the state.

```agda
correctness-acc : ∀ e m s s' r →
  (∀ x → m x < r) →
  (∀ x → s x ≡ s' (reg (m x)) ) →

  (sem-code s' (compile m r e) acc ≡ source-sem s e)
```

# 5. References.
* Correctness of a compiler for arithmetic expressions. [McCarthy and Painter 1967](http://jmc.stanford.edu/articles/mcpain/mcpain.pdf).
* Correctness of a compiler for arithmetic expressions in Lean. [Xi Wang](https://kqueue.org/blog/2020/10/15/arithcc/).
* Formalization in Coq. [Jean-Christophe Filliâtre](https://github.com/coq-contribs/mini-compiler).

