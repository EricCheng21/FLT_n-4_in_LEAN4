# Infinite Descent Blueprint

This file gives a human-readable outline of the infinite descent argument used
in the project. It is deliberately written as a mathematical proof sketch, not
as Lean code. The corresponding Lean formalization is in InfiniteDescent.lean.

## Goal

The aim is to prove that there is no normalized minimal solution of:

    a^4 + b^4 = c^2

Here normalized minimal solution means:

- a and b are nonzero.
- a is odd.
- c > 0.
- Among all solutions of x^4 + y^4 = z^2, the chosen solution has minimal |c|.

The proof proceeds by contradiction. We assume such a minimal solution exists
and then construct a smaller one.

## Step 1: Start from a minimal solution

Assume that (a,b,c) is a normalized minimal solution:

    a^4 + b^4 = c^2

The goal is to derive a contradiction by constructing a new solution (j,k,i)
such that:

    j^4 + k^4 = i^2

and:

    |i| < |c|

This would contradict the minimality of |c|.

## Step 2: Make the first Pythagorean triple

Rewrite the equation as:

    (a^2)^2 + (b^2)^2 = c^2

Thus:

    (a^2,b^2,c)

is a Pythagorean triple.

Because the original solution is minimal, a and b are coprime. Hence a^2 and
b^2 are also coprime. Since a is odd, a^2 is also odd.

Therefore this is a primitive Pythagorean triple in the correct normalized form.

## Step 3: Classify the first Pythagorean triple

By the classification of primitive Pythagorean triples, there exist integers
m and n such that:

    a^2 = m^2 - n^2
    b^2 = 2mn
    c = m^2 + n^2
    gcd(m,n) = 1

This is the first major structural step. It replaces the original equation by
parameters m and n.

## Step 4: Make the second Pythagorean triple

From:

    a^2 = m^2 - n^2

we rearrange:

    a^2 + n^2 = m^2

Thus:

    (a,n,m)

is another Pythagorean triple.

One also proves:

    gcd(a,n) = 1

So this second triple is again primitive.

## Step 5: Classify the second Pythagorean triple

Applying the primitive Pythagorean triple classification again, this time to
(a,n,m), gives integers r and s such that:

    n = 2rs
    m = r^2 + s^2
    gcd(r,s) = 1

This is the second major structural step.

## Step 6: Show that b is even

From the first classification we have:

    b^2 = 2mn

Therefore b^2 is even. Since 2 is prime, b must also be even. Write:

    b = 2b'

for some integer b'.

## Step 7: Rewrite the square equation

Using:

    b^2 = 2mn

and:

    n = 2rs

we obtain:

    b^2 = 2m(2rs) = 4mrs

Since b = 2b', we also have:

    b^2 = 4b'^2

Therefore:

    b'^2 = mrs

Equivalently:

    b'^2 = m(rs)

This is the key equation for the square-factor argument.

## Step 8: Establish the needed coprimality

From:

    m = r^2 + s^2

and:

    gcd(r,s) = 1

one obtains:

    gcd(m,rs) = 1

Thus the two factors m and rs in:

    b'^2 = m(rs)

are coprime.

## Step 9: Use the square-factor argument

We now use the elementary fact that if two coprime integers multiply to a square,
then each factor is a square up to sign.

Since:

    b'^2 = m(rs)
    gcd(m,rs) = 1

we conclude that m is a square up to sign and rs is a square up to sign.

Because m > 0, the sign ambiguity for m disappears. Hence there is an integer i
such that:

    m = i^2

Similarly, there is an integer d such that:

    rs = d^2

## Step 10: Turn r and s into fourth powers

Since:

    rs = d^2
    gcd(r,s) = 1

the same square-factor argument applies again. The factors r and s are each
squares up to sign.

Therefore their squares are fourth powers. So there exist integers j and k such
that:

    r^2 = j^4
    s^2 = k^4

The signs no longer matter after squaring.

## Step 11: Construct a new Fermat-type solution

Recall that:

    m = r^2 + s^2

But we also have:

    m = i^2

Therefore:

    i^2 = r^2 + s^2

Using:

    r^2 = j^4
    s^2 = k^4

we get:

    i^2 = j^4 + k^4

Equivalently:

    j^4 + k^4 = i^2

Thus (j,k,i) is a new solution of the same auxiliary Fermat equation.

## Step 12: Prove the new solution is smaller

From the first classification:

    c = m^2 + n^2

Since n is nonzero, we have n^2 > 0, so:

    c > m^2

Since m = i^2, this implies that the new square side is smaller:

    |i| < |c|

The Lean proof phrases this using Int.natAbs, because it works over integers.

## Step 13: Use minimality

The original solution (a,b,c) was assumed to be minimal. Therefore every solution
(x,y,z) of the same auxiliary equation must satisfy:

    |c| <= |z|

Apply this to the new solution (j,k,i). We obtain:

    |c| <= |i|

## Step 14: Contradiction

Step 12 gives:

    |i| < |c|

Step 13 gives:

    |c| <= |i|

These inequalities cannot both hold. This contradiction shows that the assumed
normalized minimal solution cannot exist.

## Summary

The descent argument starts from a minimal solution, converts it into a
Pythagorean triple, classifies that triple, creates a second Pythagorean triple,
classifies again, and uses coprimality to force certain factors to be squares.
This produces a new solution with a smaller square side, contradicting
minimality.

The Lean file InfiniteDescent.lean formalizes this blueprint as a sequence of
small helper lemmas followed by the theorem no_normalized_minimal.
