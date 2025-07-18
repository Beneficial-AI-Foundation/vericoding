//ATOM

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


// SPEC

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
  requires 0 <= i <= i+n <= a.Length
  requires forall p,q | i <= p < q < i+n :: a[p] <= a[q]
  requires Is2Pow(n+1)
  ensures i <= k <= i+n
  ensures forall r | i <= r < k :: a[r] < x
  ensures forall r | k <= r < i+n :: a[r] >= x
{
}
