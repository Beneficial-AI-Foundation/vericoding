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
    /* code modified by LLM (iteration 1): base case returns i which satisfies bounds */
    k := i;
  } else {
    /* code modified by LLM (iteration 1): calculate midpoint for binary search */
    var mid := i + n/2;
    
    /* code modified by LLM (iteration 1): establish key properties for recursive calls */
    assert n >= 1;
    assert Is2Pow(n+1);
    assert (n+1) % 2 == 0 && Is2Pow((n+1)/2);
    assert n % 2 == 1;
    assert n/2 == (n-1)/2;
    assert n/2 + 1 == (n+1)/2;
    assert Is2Pow(n/2 + 1);
    
    if a[mid] < x {
      /* code modified by LLM (iteration 1): search right half with correct size */
      k := Search2PowRecursive(a, mid+1, n/2, x);
      
      /* code modified by LLM (iteration 1): verify bounds and establish postconditions */
      assert mid+1 + n/2 == i + n/2 + 1 + n/2 == i + n;
      assert forall r | mid+1 <= r < k :: a[r] < x;
      assert forall r | k <= r < mid+1+n/2 :: a[r] >= x;
      assert mid+1+n/2 == i+n;
      
      /* code modified by LLM (iteration 1): establish left part property using sortedness */
      assert a[mid] < x;
      assert forall r | i <= r <= mid :: a[r] <= a[mid] < x;
      assert forall r | i <= r < mid+1 :: a[r] < x;
      assert forall r | i <= r < k :: a[r] < x;
    } else {
      /* code modified by LLM (iteration 1): search left half */
      k := Search2PowRecursive(a, i, n/2, x);
      
      /* code modified by LLM (iteration 1): establish postconditions */
      assert forall r | i <= r < k :: a[r] < x;
      assert forall r | k <= r < i + n/2 :: a[r] >= x;
      
      /* code modified by LLM (iteration 1): extend right part property using sortedness */
      assert a[mid] >= x;
      assert forall r | mid <= r < i+n :: a[r] >= a[mid] >= x;
      assert k <= i + n/2;
      assert i + n/2 <= mid;
      assert forall r | k <= r < i+n :: a[r] >= x;
    }
  }
}