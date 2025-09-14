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
lemma lemma_Search1000Helper(n: int, m: int)
    requires 0 <= n <= m
    ensures n <= (n + m) / 2 <= m
{
}

lemma lemma_Search1000Helper2(n: int, m: int)
    requires 0 <= n < m
    ensures n < (n + m) / 2 < m || (n + 1 == m && (n + m) / 2 == n)
{
    if n + 1 == m {
    }
}

lemma lemma_ArraySortedImpliesTransitive(a: array<int>, p: int, q: int, r: int)
    requires 0 <= p < q < r < a.Length
    requires forall i,j | 0 <= i < j < a.Length :: a[i] <= a[j]
    ensures a[p] <= a[q] <= a[r]
{
}

lemma lemma_ArraySortedInductive(a: array<int>, i: int, j: int)
    requires 0 <= i <= j < a.Length
    requires forall p,q | 0 <= p < q < a.Length :: a[p] <= a[q]
    ensures a[i] <= a[j]
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := 1000;
  
  while low < high
    invariant 0 <= low <= high <= 1000
    invariant forall r | 0 <= r < low :: a[r] < x
    invariant forall r | high <= r < 1000 :: a[r] >= x
  {
    var mid := (low + high) / 2;
    
    if a[mid] < x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  k := low;
}
// </vc-code>

