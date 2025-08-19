method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
  /* code modified by LLM (iteration 1): added decreases clause to prove termination */
  decreases j - i
{
  if i == j {
    k := i;
  } else {
    var mid := (i + j) / 2;
    if a[mid] >= x {
      k := SearchRecursive(a, mid + 1, j, x);
    } else {
      k := SearchRecursive(a, i, mid, x);
    }
  }
}