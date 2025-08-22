// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
// SPEC 
// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
{
}


// Is2Pow(n) is true iff n==2^k for some k>=0.
//ATOM_PLACEHOLDER_Is2Pow

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
//ATOM_PLACEHOLDER_Search2PowLoop

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
//ATOM_PLACEHOLDER_Search2PowRecursive

