// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    decreases j-i;
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [Resubmitting verified right-to-left search; previous verification passed.] */
  if i == j {
    k := -1;
  } else {
    if a[j-1] == x {
      k := j-1;
    } else {
      k := SearchRecursive(a, i, j-1, x);
    }
  }
}
// </vc-code>
