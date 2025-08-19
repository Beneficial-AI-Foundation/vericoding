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
  /* code modified by LLM (iteration 1): added decreases clause to prove termination */
  decreases n
{
  if n == 0 {
    return i;
  }
  
  var mid := i + n / 2;
  
  if a[mid] < x {
    /* code modified by LLM (iteration 1): added assertions to help prove postconditions */
    assert forall r | i <= r <= mid :: a[r] < x;
    k := Search2PowRecursive(a, mid + 1, n / 2, x);
  } else {
    /* code modified by LLM (iteration 1): added assertion to help prove postconditions */
    assert a[mid] >= x;
    k := Search2PowRecursive(a, i, n / 2, x);
  }
}