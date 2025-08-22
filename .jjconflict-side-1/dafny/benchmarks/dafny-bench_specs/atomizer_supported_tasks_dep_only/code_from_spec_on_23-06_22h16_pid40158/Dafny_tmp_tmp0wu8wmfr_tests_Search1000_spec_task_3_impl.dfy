// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
//ATOM Search1000
method Search1000( a: array<int>, n: int, x: int ) returns ( k: int )
    requires 0 <= n <= a.Length;
    requires forall p,q | 0 <= p < q < n :: a[p] <= a[q];
    ensures 0 <= k <= n;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < n :: a[r] >= x;
{
    var lo, hi := 0, n;
    while lo < hi
        invariant 0 <= lo <= hi <= n;
        invariant forall r | 0 <= r < lo :: a[r] < x;
        invariant forall r | hi <= r < n :: a[r] >= x;
    {
        var mid := (lo + hi) / 2;
        if a[mid] < x {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    k := lo;
}

// Is2Pow(n) is true iff n==2^k for some k>=0.
//ATOM Is2Pow
predicate Is2Pow( n: int )
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
//ATOM Search2PowLoop
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{
    var lo, hi := i, i+n;
    while lo < hi
        invariant i <= lo <= hi <= i+n;
        invariant forall r | i <= r < lo :: a[r] < x;
        invariant forall r | hi <= r < i+n :: a[r] >= x;
    {
        var mid := (lo + hi) / 2;
        if a[mid] < x {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    k := lo;
}

/* code modified by LLM (iteration 1): Fixed helper lemma to correctly handle the Is2Pow property for recursive halving */
lemma Is2PowHalving(n: int)
    requires n > 0 && Is2Pow(n+1)
    ensures Is2Pow(n/2 + 1)
{
    if n == 1 {
        assert n/2 + 1 == 1;
        assert Is2Pow(1);
    } else {
        assert n >= 2;
        assert Is2Pow(n+1);
        assert (n+1) >= 2;
        assert (n+1) % 2 == 0;
        assert Is2Pow((n+1)/2);
        
        // Since Is2Pow(n+1) and n+1 > 1, we know n+1 is even
        // This means n is odd, so n = 2m+1 for some m
        // Therefore n/2 = m and n/2 + 1 = m + 1
        // Since n+1 = 2m+2 = 2(m+1), we have (n+1)/2 = m+1 = n/2 + 1
        assert (n+1)/2 == n/2 + 1;
        assert Is2Pow(n/2 + 1);
    }
}

//IMPL Search2PowRecursive
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
    decreases n
{
    if n == 0 {
        k := i;
    } else {
        var mid := i + n/2;
        /* code modified by LLM (iteration 1): Added lemma call to establish Is2Pow precondition for recursive calls */
        Is2PowHalving(n);
        
        if a[mid] < x {
            /* code modified by LLM (iteration 1): Recursive call on right half with corrected bounds */
            k := Search2PowRecursive(a, mid + 1, n/2, x);
        } else {
            /* code modified by LLM (iteration 1): Recursive call on left half with corrected bounds */
            k := Search2PowRecursive(a, i, n/2, x);
        }
    }
}