// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): switched to an iterative implementation searching from right to left */
{
  var current := j - 1;
  while current >= i
    decreases current      
    invariant i - 1 <= current < j
    invariant forall r | current < r < j :: a[r] != x
  {
    if a[current] == x {
      k := current;
      return;
    }
    current := current - 1;
  }
  k := -1;
}
// </vc-code>
