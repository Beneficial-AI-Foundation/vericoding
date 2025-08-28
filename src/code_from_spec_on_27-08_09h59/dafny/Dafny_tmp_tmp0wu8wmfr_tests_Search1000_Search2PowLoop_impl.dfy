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

// <vc-helpers>
lemma Is2PowProperties(n: int)
    requires Is2Pow(n)
    ensures n >= 1
    decreases n
{
    if n == 1 {
    } else {
        Is2PowProperties(n/2);
    }
}

lemma Is2PowDivisionProperty(n: int)
    requires Is2Pow(n) && n > 1
    ensures Is2Pow(n/2)
    decreases n
{
}

lemma Is2PowHalfProperty(n: int)
    requires Is2Pow(n+1) && n >= 1
    ensures Is2Pow((n+1)/2)
    decreases n
{
    Is2PowDivisionProperty(n+1);
}

lemma Is2PowSubtraction(n: int)
    requires Is2Pow(n+1) && n >= 1
    ensures Is2Pow((n+1)/2)
    ensures (n+1)/2 - 1 >= 0
    ensures Is2Pow(((n+1)/2 - 1) + 1)
    decreases n
{
    Is2PowDivisionProperty(n+1);
}

lemma SizeReductionLemma(size: int)
    requires size >= 1 && Is2Pow(size + 1)
    ensures size >= 2 ==> Is2Pow((size + 1) / 2)
    ensures size >= 2 ==> Is2Pow(size - (size + 1) / 2 + 1)
    decreases size
{
    if size >= 2 {
        Is2PowDivisionProperty(size + 1);
        var half := (size + 1) / 2;
        var remaining := size - half + 1;
        assert remaining == half - 1;
        assert Is2Pow(half);
        if remaining > 0 {
            assert remaining + 1 == half;
            assert Is2Pow(remaining + 1);
        }
    }
}

lemma Is2PowArithmetic(n: int)
    requires Is2Pow(n) && n > 1
    ensures n/2 >= 1
    ensures Is2Pow(n/2)
{
    Is2PowDivisionProperty(n);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    k := i;
    var size := n;
    
    while size > 0
        invariant 0 <= size <= n
        invariant i <= k <= i + n - size
        invariant forall r | i <= r < k :: a[r] < x
        invariant forall r | k + size <= r < i + n :: a[r] >= x
        invariant Is2Pow(size + 1)
        decreases size
    {
        Is2PowProperties(size + 1);
        var half := (size + 1) / 2 - 1;
        
        if size > 1 {
            SizeReductionLemma(size);
            assert Is2Pow(size - (size + 1) / 2 + 1);
        }
        
        if k + half < i + n && a[k + half] < x {
            k := k + half + 1;
            size := size - half - 1;
            assert size == size - (size + 1) / 2 + 1;
        } else {
            size := half;
            assert size == (size + 1) / 2 - 1;
            assert Is2Pow(size + 1);
        }
    }
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.