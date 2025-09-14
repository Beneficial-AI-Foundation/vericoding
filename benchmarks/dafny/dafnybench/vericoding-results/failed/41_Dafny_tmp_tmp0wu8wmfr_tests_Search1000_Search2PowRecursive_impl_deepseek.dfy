// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
lemma lemma_EmptyRange(a: array<int>, i: int, x: int)
    ensures forall r | i <= r < i :: a[r] < x
{
}

lemma lemma_SingleElement(a: array<int>, i: int, x: int)
    requires 0 <= i < a.Length
    ensures (a[i] < x ==> forall r | i <= r < i+1 :: a[r] >= x)
{
    if a[i] < x {
        forall r | i <= r < i+1
            ensures a[r] >= x
        {
            assert r == i;
        }
    }
}

lemma lemma_Transitivity(a: array<int>, i: int, j: int, k: int, x: int)
    requires i <= j <= k
    requires forall r | i <= r < j :: a[r] < x
    requires forall r | j <= r < k :: a[r] >= x
    ensures forall r | i <= r < k :: a[r] < x || a[r] >= x
{
    forall r | i <= r < k
        ensures a[r] < x || a[r] >= x
    {
        if r < j {
            assert a[r] < x;
        } else {
            assert a[r] >= x;
        }
    }
}

lemma lemma_IndexInRange(a: array<int>, i: int, n: int, idx: int)
    requires 0 <= i <= i+n <= a.Length
    requires i <= idx < i+n
    ensures 0 <= idx < a.Length
{
}
// </vc-helpers>

// <vc-spec>
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    decreases n;
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        k := i;
        lemma_EmptyRange(a, i, x);
    } else {
        var m := (n - 1)/2;
        lemma_IndexInRange(a, i, n, i + m);
        if a[i + m] < x {
            var subk := Search2PowRecursive(a, i + m + 1, m, x);
            k := subk;
            lemma_Transitivity(a, i, i + m + 1, subk, x);
        } else {
            var subk := Search2PowRecursive(a, i, m, x);
            k := subk;
            lemma_Transitivity(a, i, subk, i + m, x);
        }
    }
}
// </vc-code>

