# OhTT

This is an experimental project that aims to be a typechecker for Observational Type Theory with support for Quotient Inductive-Inductive Types.

## Motivation

I am reading Thorsten Altenkirch and Ambrus Kaposi et al.'s "type theory in type theory" series  of papers, and I am feeling uncomfortable with the fact that their formalization are based on a bunch of postulated rules in Agda.

## Features

We have an proof irrelevant observational equality `a ~{A} b`, for QITs, the equality between path can be computed out as following:

```agda
quotient data I : Type where 
  | i0 : I 
  | i1 : I 
  | seg : i0 ~{I} i1
```

Then `i0 ~{I} i1` is a canonical form with a single constructor `seg`.

---

This is just an experimental project currently, and I will make it better someday.
Known missing parts:
- guardness checking for apd clause
- proof-irrelevance
- observational computational rules of OTT
