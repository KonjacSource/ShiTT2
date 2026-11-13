#import "@preview/diatypst:0.9.3": *
#import "@preview/color-my-agda:0.2.0": init-color-my-agda

#show: init-color-my-agda

#let nl-yellow = rgb("#F7D544")
#let nl-brown = rgb("#7A4A1E")
#let nl-cream = rgb("#FFF6D6")


#show: slides.with(
  title: "Towards a Dependently Typed Language with Observational Equality and QIITs", // Required
  // date: "01.07.2024",
  authors: ("Qu Zhuoyuan"),
  title-color: nl-yellow.darken(20%),
  theme: "full",
  count: none,
  toc: false,
)

#let nailoong-face(w) = {
  let h = w * 0.80
  let eye(cx) = {
    let ew = w * 0.20
    let eh = h * 0.25
    let cy = h * 0.47
    place(top + left, dx: w * cx - ew / 2, dy: cy - eh / 2,
      ellipse(width: ew, height: eh, fill: rgb("#CFE0A0")))
    place(top + left, dx: w * cx - w * 0.05, dy: cy - h * 0.04,
      ellipse(width: w * 0.1, height: h * 0.13, fill: black))
  }
  box(width: w, height: h, clip: true, {
    eye(0.27)
    eye(0.78)
    place(top + left, dx: w * 0.39, dy: h * 0.7,
      curve(
        stroke: 0.6pt + rgb("#8A5A1A"),
        curve.move((0pt, 0pt)),
        curve.line((w * 0.14, h * 0.045)),
        curve.line((w * 0.30, h * 0.005)),
      ))
  })
}

#set page(foreground: place(top + right, dx: -0.5cm, dy: 0.02cm, nailoong-face(0.95cm)))
// #set text(fill: nl-brown)
// #show strong: set text(fill: nl-yellow.darken(30%))
// #show emph: set text(fill: nl-yellow.darken(35%))
// #show footnote: set text(fill: nl-yellow.darken(30%))


#show raw.where(block: true): set text(size: 7pt)
#show raw.line: it => {
  show regex("\bCx\b|\bSb\b|\bTy\b|\bTm\b|\bI\b|\bℕ\b|\bℤ\b|\bType\b|\bProp\b|\bElim\b|\bMaybe\b|\bBool\b"): set text(fill: purple)
  show regex("\bf\b|\bJust\b|\bNothing\b|\babs\b|\b0\b|\b1\b"): set text(fill: blue)
  show regex("\bopen\b"): set text(fill: green)
  show regex("\bap\b"): set text(fill: color.fuchsia)
  it
}

// Suggest

// + explain QIT
// + ap name is confusing
// + remove last two slides
// + too yellow

== Background

A Quotient Inductive Type (QIT) is 
- an inductive type with *equalities between its elements*.
- an *initial algebra* of an *algebraic theory*
- a set level *higher inductive type*. i.e. every path is trivial.

*Examples.*

```agda
data ℤ : Type where
  pos    : ℕ → ℤ
  neg    : ℕ → ℤ
  eqZero : pos 0 ≡ neg 0
```
  
```agda
-- Free Monoid
data Monoid : Type where
  1 : Monoid
  _*_ : Monoid → Monoid → Monoid
  idl : (x : Monoid) → 1 * x ≡ x
  idr : (x : Monoid) → x * 1 ≡ x
  assoc : (x y z : Monoid) → (x * y) * z ≡ x * (y * z)
```
  
== Background

Eliminator of QITs.

- QITs introduce new equalities
- Eliminator of QITs must respect these equalities (*congruence*)
  ```agda
  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ```

- Each eliminator must show that it respects the equalities introduced by the QIT

*Example.*
```agda
recℤ :  (D : Type) →
        (pD : (n : ℕ) → D) →
        (nD : (n : ℕ) → D) →
        (eqZeroD : pD 0 ≡ nD 0) →
        ℤ → D
```

== Background

A Quotient Inductive-Inductive Type (QIIT) is
- a generalization of QIT where multiple types are defined simultaneously
- an *initial algebra* of a *generalized algebraic theory* (GAT)

*Example of GAT:*

- Category
  - Two sorts: *Obj* and *Hom*
  - Operations: idenity morphisms, compositions
  - Laws as qualities

- Type Theory
  - Four sorts: *Cx*, *Sb*, *Ty*, *Tm*
  - Operations: context structures, identity substitutions and compositions, type formations, term constructors and eliminators etc.
  - Conversions as equalities

== Background
- Altenkirch. Kaposi. _Type theory in type theory using quotient inductive types_ #footnote[https://dl.acm.org/doi/10.1145/2837614.2837638]

```agda
data Cx : Type where
  𝟏   : Cx 
  _,_ : (Γ : Cx) → Ty Γ → Cx

data Sb : Cx → Cx → Type where
  id : (Γ : Cx) → Sb Γ Γ
  ...

data Ty : Cx → Type where
  _[_]   : (A : Ty Γ) (γ : Sb Δ Γ) → Ty Δ
  sub-id : (A : Ty Γ) → A [ id ] ≡ A
  Π      : (A : Ty Γ) (B : Ty (Γ ⸴ A)) → Ty Γ
  ...

data Tm : (Γ : Cx) → Ty Γ → Type where
  β : {A : Ty Γ} {B : Ty (Γ ⸴ A)} (b : Tm (Γ ⸴ A) B) → app (lam b) ≡ b 
  ... 
```

== Benefits

- `Cx-Sb-Ty-Tm` is initial algebra of CwF.

- Displayed algebras and models can be defined as functions from `Cx-Sb-Ty-Tm` to other types.

- We can extract algorithms from the proof of certain meta-properties 

- Some meta-properties (e.g. consistency) are much easier to prove in this setting.

== But

- We need "Quotient Interleaved Inductive-Inductive Types" (QIIITs)

```agda
...
data Sb where 
  id : Sb Γ Γ <---------------------------------╮
                                                |
data Ty where                                   |
  _[_] : (A : Ty Γ) (γ : Sb Δ Γ) → Ty Δ  <------+---------------------╮
  sub-id : (A : Ty Γ) → A [ id ] ≡ A            |                     |
                            ^^------------------╯                     |
data Sb where                                                         |
  _⸴_ : (γ : Sb Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ γ ])) → Sb Δ (Γ ⸴ A)   |         
...                                          ^---^--------------------╯
```

- Eliminator of an QIIIT is a set of functions with interleaved clauses
  - Later clauses can depend on definitional equalities introduced by earlier clauses
- This can be solved by using Szumi Xie's trick
  - Or we can directly implement a prover supporting QIIITs

== But

- Transport hell

`Tm` is indexed by `Ty`, which is indexed by `Cx`, we would meet a very serious transport hell problem when we try to do proofs in this setting.

- Solution: Observational Type Theory (OTT)
  - transport can be computed by observing the types

\
\
- Other solution: 
  - Make some of quotient equalities hold definitionally 

    Kaposi. Pujet. _Type Theory in Type Theory using a Strictified Syntax_

== A Prover with OTT and QIITs

We want a dependently typed language with
- Observational Equality
- Quotient Interleaved Indexed Inductive-Inductive Types


\ \
- We need a syntax for pattern matching on QITs.

== Elimination of QITs

In CuTT.

```agda
data ℤ : Type where
  pos    : ℕ → ℤ
  neg    : ℕ → ℤ
  eqZero : pos 0 ≡ neg 0 
  --     ^ (i : I) → {ℤ | i = 0 → pos 0, i = 1 → neg 0}

abs : ℤ → ℕ
abs (pos n)    := n
abs (neg n)    := n
abs (eqZero i) := ?

boundary conditions:
i = 0 ⊢ ? = abs (pos 0)
i = 1 ⊢ ? = abs (neg 0) 
```

- But in OTT, the equality is not an extension type, so we cannot use the boundary checking to check the elimination of QITs.

== Elimination of QITs

Solution: Quotient Equality as Inductive Proposition

```agda
data ℤ : Type where
  pos    : ℕ → ℤ
  neg    : ℕ → ℤ

data _~ᴢ_ : ℤ → ℤ → Prop where
  eqZero : (pos 0) ~ᴢ (neg 0)

a ~{ℤ} b := a ~ᴢ b 

abs : ℤ → ℕ
abs (pos n)    := n
abs (neg n)    := n
```

#let ap = $bold("ap")$
and we have 

$
  (f : A → B quad A "is a QIT" quad f "is an eliminator")
  /
  (ap f :  x ~ y → f x ~ f y )
$

== Elimination of QITs

```agda
abs : ℤ → ℕ
abs (pos n)    := n
abs (neg n)    := n
```

$
  (f : A → B quad A "is a QIT" quad f "is an eliminator")
  /
  (ap f : " " x ~ y → f x ~ f y )
$

Type checker found a missing clause for $ap$ !

```agda
ap abs eqZero := ?

? : abs (pos 0) ~ abs (neg 0)
```

== How to check?

- Löh. Hinze. _Open Data Types and Open Functions_
  - An Haskell extension proposal (psudo syntax here)
    ```haskell
    open data Expr = Num Int 
    open eval :: Expr -> Int
    eval (Num n) = n
    -- Another module can add new constructors and clauses
    data Expr += Add Expr Expr
    eval (Add e1 e2) = eval e1 + eval e2
    ```
  
== How to check?

- Suppose we have an open inductive type `Elim` and open functions `run` and `ap`
  
  ```agda
  open data Elim : (A B : Type) → Type 
  open run : Elim A B → A → B
  open ap : (f : Elim A B) → x ~ y → run f x ~ run f y
  ```
  
  When we define `abs`, we actually defined
  ```agda
  data Elim += (abs : Elim ℤ ℕ)
  run abs (pos n) := n
  run abs (neg n) := n
  ap abs eqZero := refl
  ```

== How to check?  

For practical implementation
- Generating missing $ap$ clauses while coverage checking, 
  
  e.g.
  ```agda
  abs (pos n)    := n
  abs (neg n)    := n
  ```
  `abs` is splitting on its argument which is a QIT, so we need to generate the missing $ap$ clause for `abs`:
  ```agda
  ap abs (_: x ~ y) : abs x ~ abs y
  ```

- User must fill all the missing $ap$ clauses before the module ends.

// == How to check?

// This approach is quite smart, for example, 
// ```agda
// data I : Type where
//   0 : I
//   1 : I
//   seg : 0 ~ 1

// f : Bool → I → ... 
// f true  i := ...
// f false 0 := f0
// f false 1 := f1
// ```
// we only have the following missing $ap$ clause for `f`:
// ```agda
// ap (f false) seg : f0 ~ f1
// ```

// == Nested pattern

// - Nested pattern is tricky

// ```agda
// f : Maybe I → ... 
// f (Just 0) := ...
// f (Just 1) := ...
// f Nothing := ...

// missing ap is 
// ap f (ap Just (_ : x ~ y)) : f (Just x) ~ f (Just y)
// ```

// Hence `ap` is also a pattern.

// ```agda
// data _~_ : I → I → Prop where
//   seg : 0 ~ 1
//   ap : (f : A → B) → x ~ y → f x ~ f y
// ```

== Status and Future Works

- We are implementing a prototype of this idea.

- We want to reason about the soundness of this pattern matching algorithm by translating it to eliminators (as in Goguen et al. _Eliminating Dependent Pattern Matching_).

- We want to use this prover to formalize the meta-theories of various type theories. including canonicity and normalization with gluing techniques.


- Repo is here: 
  
  https://github.com/KonjacSource/ShiTT2/tree/ott

// == Other Related References

// - QIITs is compatible with OTT

//   Kaposi. Xie. _Quotient Inductive-Inductive Types in the Setoid Model_

