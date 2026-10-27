-

The pattern mathcing

f : Nat -> Bool
f zero = true
f (suc _) = false

the application

for a neutral term n,
f (cast Nat Nat _ n) should stuck, even though we have cast-refl, by which `f (cast Nat Nat _ n)` is convertible to `f n`, They are both normal forms in our system, and can be decided to be equal

when n is reduce to, for example, `zero`, then `f (cast Nat Nat _ zero)` is convertible to `f zero`, by `cast-zero`, not by `cast-refl`, and the, the pattern matching can be done.

For indexed inductive types, this situation is more complicated, it seems that we have to adapt the method in Cubical Agda. We need an extra constructor `castX` for each indexed inductive type, and extend the pattern matching to `castX` as well. And we use `f-castX` in this case. Unlike Agda, I think we can always do the pattern matching extension.

And regularity still holds.
