// IMPL
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:  Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//  dafny H2-skeleton.dfy
// or
//  compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
{
  if i == j {
    k := i;
  } else if a[i] < x {
    k := i;
  } else {
    var mid := i + (j - i) / 2;
    /* code modified by LLM (iteration 1): Added assertion to establish mid bounds and improve reasoning */
    assert i <= mid < j;
    
    if a[mid] >= x {
      k := SearchRecursive(a, mid + 1, j, x);
      /* code modified by LLM (iteration 1): Added comprehensive assertions for the first branch */
      // Since array is descending and a[mid] >= x, all elements from i to mid are >= x
      assert forall r | i <= r <= mid :: a[r] >= a[mid] >= x;
      // This gives us the property for elements before k in the range [i, mid+1)
      assert forall r | i <= r < mid + 1 :: a[r] >= x;
      // The recursive call ensures properties for [mid+1, j), we need to combine them
      assert forall r | mid + 1 <= r < k :: a[r] >= x;
      assert forall r | k <= r < j :: a[r] < x;
    } else {
      k := SearchRecursive(a, i, mid, x);
      /* code modified by LLM (iteration 1): Added comprehensive assertions for the second branch */
      // Since array is descending and a[mid] < x, all elements from mid to j-1 are < x
      assert forall r | mid <= r < j :: a[r] <= a[mid] < x;
      // The recursive call gives us k in [i, mid] with proper properties
      assert forall r | i <= r < k :: a[r] >= x;
      assert forall r | k <= r < mid :: a[r] < x;
      // We need to extend the second property to include [mid, j)
      assert forall r | k <= r < j :: a[r] < x;
    }
  }
}