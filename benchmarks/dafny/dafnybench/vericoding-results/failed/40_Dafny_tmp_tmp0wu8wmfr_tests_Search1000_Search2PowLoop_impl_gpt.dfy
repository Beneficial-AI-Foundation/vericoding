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
// No helper code needed
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
  var l := i;
  var u := i + n;
  while l < u
    invariant i <= l <= u <= i + n
    invariant forall r :: i <= r < l ==> a[r] < x
    invariant forall r :: u <= r < i + n ==> a[r] >= x
    decreases u - l
  {
    var m := l + (u - l) / 2;
    assert 0 <= (u - l) / 2 < u - l;
    assert l <= m < u;
    assert i <= m < i + n;
    assert 0 <= m < a.Length;
    if a[m] < x {
      assert forall r :: i <= r <= m ==> a[r] < x
      {
        forall r | i <= r <= m
          ensures a[r] < x
        {
          if r == m {
          } else if r < l {
            assert i <= r < l;
          } else {
            assert i <= r < m < i + n;
            assert a[r] <= a[m];
          }
        }
      };
      l := m + 1;
    } else {
      assert forall r :: m <= r < i + n ==> a[r] >= x
      {
        forall r | m <= r < i + n
          ensures a[r] >= x
        {
          if r == m {
          } else {
            assert i <= m < r < i + n;
            assert a[m] <= a[r];
          }
        }
      };
      u := m;
    }
  }
  k := l;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.