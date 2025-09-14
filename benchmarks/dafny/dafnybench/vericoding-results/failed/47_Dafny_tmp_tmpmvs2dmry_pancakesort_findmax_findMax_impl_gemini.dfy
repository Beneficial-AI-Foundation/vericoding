// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [using a for-loop, as the previous verified implementation failed due to unrelated compilation warnings] */
  r := 0;
  for i := 1 .. n
    invariant 1 <= i <= n
    invariant 0 <= r < i
    invariant forall k :: 0 <= k < i ==> a[r] >= a[k]
  {
    if a[i] > a[r] {
      r := i;
    }
  }
}
// </vc-code>
