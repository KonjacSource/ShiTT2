# OhTT

This is an experimental project that aims to be a typechecker for Observational Type Theory with support for Quotient Inductive-Inductive Types.

## Syntax

HoTT Book styled syntax, with standalone apd clauses.

Example

```agda
data Bool : U where
| true : Bool
| false : Bool

quotient data I : U where 
| i0 : I 
| i1 : I 
| seg : i0 ~ i1 

def f : Bool -> I -> Nat
| true i0 = zero 
| true i1 = zero
| false h = suc zero

def apd for f 
| (f true) {x} {y} seg = rfl _
```

Note. In this example, you have to give an apd clause for (f true) to show congruence, but no need for (f false).
