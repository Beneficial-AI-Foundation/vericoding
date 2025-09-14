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
lemma Is2PowPreserved(n: int)
    requires Is2Pow(n+1)
    requires n > 0
    ensures Is2Pow((n-1)/2 + 1)
{
    assert n+1 >= 2;
    assert (n+1) % 2 == 0;
    assert Is2Pow((n+1)/2);
    assert (n+1)/2 == (n-1)/2 + 1;
}

lemma DivisionProperties(n: int)
    requires Is2Pow(n+1)
    requires n > 0
    ensures (n-1)/2 >= 0
    ensures (n-1)/2 < n
{
    assert n+1 >= 2;
    assert n >= 1;
}

lemma SizeReduction(size: int)
    requires Is2Pow(size + 1)
    requires size > 0
    ensures Is2Pow((size - 1) / 2 + 1)
{
    Is2PowPreserved(size);
}
// </vc-helpers>

// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
    k := i;
    var left := i;
    var right := i + n;
    var size := n;
    
    while size > 0
        invariant left <= right
        invariant i <= left <= right <= i + n
        invariant k == left
        invariant forall r | i <= r < left :: a[r] < x
        invariant forall r | right <= r < i + n :: a[r] >= x
        invariant Is2Pow(size + 1)
        invariant right - left == size
        decreases size
    {
        var mid := left + (size - 1) / 2;
        
        if a[mid] < x {
            left := mid + 1;
        } else {
            right := mid;
        }
        
        if size > 0 {
            SizeReduction(size);
        }
        
        size := (size - 1) / 2;
        k := left;
    }
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.