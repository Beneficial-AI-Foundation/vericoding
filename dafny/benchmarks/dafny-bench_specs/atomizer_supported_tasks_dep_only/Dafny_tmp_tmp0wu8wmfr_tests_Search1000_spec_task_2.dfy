// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
//ATOM_PLACEHOLDER_Search1000

// Is2Pow(n) is true iff n==2^k for some k>=0.
// ATOM 

// Is2Pow(n) is true iff n==2^k for some k>=0.
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
// SPEC 

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{
}


// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
//ATOM_PLACEHOLDER_Search2PowRecursive

