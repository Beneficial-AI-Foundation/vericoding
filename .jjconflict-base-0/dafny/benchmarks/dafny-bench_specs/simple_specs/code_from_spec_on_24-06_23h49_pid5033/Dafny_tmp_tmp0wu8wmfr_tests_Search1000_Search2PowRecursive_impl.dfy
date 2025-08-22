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


//IMPL

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
  if n == 0 {
    k := i;
  } else {
    var mid := i + n / 2;
    /* code modified by LLM (iteration 3): Fixed power-of-2 calculations and bounds */
    assert n >= 1;
    assert Is2Pow(n+1);
    // Since n+1 is a power of 2 and n+1 > 1, we have n+1 = 2^m for some m >= 1
    // Therefore n = 2^m - 1, and n/2 = (2^m - 1)/2 = 2^(m-1) - 1 (when m >= 1)
    // This means n/2 + 1 = 2^(m-1), so Is2Pow(n/2 + 1) holds
    assert Is2Pow(n/2 + 1);
    
    if a[mid] < x {
      /* code modified by LLM (iteration 3): Fixed right half recursive call */
      var right_start := mid + 1;
      var right_size := n - n/2 - 1;
      // right_size = n - n/2 - 1 = (2^m - 1) - (2^(m-1) - 1) - 1 = 2^(m-1) - 1
      // So right_size + 1 = 2^(m-1)
      assert right_size == n/2;
      assert Is2Pow(right_size + 1);
      assert right_start + right_size == i + n;
      k := Search2PowRecursive(a, right_start, right_size, x);
      /* code modified by LLM (iteration 3): Establish postcondition for left part */
      assert forall r | i <= r < right_start :: a[r] < x;
    } else {
      /* code modified by LLM (iteration 3): Fixed left half recursive call */
      var left_size := n / 2;
      assert Is2Pow(left_size + 1);
      k := Search2PowRecursive(a, i, left_size, x);
      /* code modified by LLM (iteration 3): Establish postcondition for right part */
      assert a[mid] >= x;
      assert forall r | mid < r < i+n :: a[r] >= x;
      assert forall r | mid <= r < i+n :: a[r] >= x;
    }
  }
}