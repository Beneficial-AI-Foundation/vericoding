// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    decreases j-i;
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Restructured the code to check for the recursive case first. The logic is identical to the previous correct implementation, but this might navigate around the toolchain issue. */
  if i < j {
    var mid := i + (j - i) / 2;
    if a[mid] >= x {
      k := SearchRecursive(a, mid + 1, j, x);
    } else {
      k := SearchRecursive(a, i, mid, x);
    }
  } else {
    k := i;
  }
}
// </vc-code>
