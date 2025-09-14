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
lemma Is2PowDivision(n: int)
    requires n > 1
    requires Is2Pow(n)
    ensures Is2Pow(n/2)
{
    // Follows directly from the definition of Is2Pow
}

lemma Is2PowProperties(n: int)
    requires n >= 0
    requires Is2Pow(n+1)
    ensures n == 0 || (n > 0 && n % 2 == 1 && Is2Pow((n+1)/2))
{
    if n == 0 {
        // n+1 == 1, which is 2^0
    } else {
        // n+1 is a power of 2 greater than 1
        // So n+1 is even and (n+1)/2 is also a power of 2
        assert (n+1) % 2 == 0;
        Is2PowDivision(n+1);
    }
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
    var lo := i;
    var hi := i + n;
    var size := n;
    
    while size > 0
        invariant i <= lo <= hi <= i + n
        invariant hi - lo == size
        invariant Is2Pow(size + 1)
        invariant forall r | i <= r < lo :: a[r] < x
        invariant forall r | hi <= r < i + n :: a[r] >= x
        invariant forall p,q | lo <= p < q < hi :: a[p] <= a[q]
    {
        Is2PowProperties(size);
        var mid := lo + size / 2;
        
        if a[mid] < x {
            lo := mid + 1;
        } else {
            hi := mid;
        }
        
        size := size / 2;
    }
    
    k := lo;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.