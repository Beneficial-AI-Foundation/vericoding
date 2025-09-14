// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): adjusted loop invariant to fix verification error */
  sum := 0;
  max := 0;
  if N == 0 {
    return;
  }
  
  sum := a[0];
  max := a[0];
  var i := 1;
  while i < N
    invariant 1 <= i <= N
    invariant max >= 0
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant exists k :: 0 <= k < i && a[k] == max
    invariant sum <= i * max
  {
    if a[i] > max {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}
// </vc-code>
