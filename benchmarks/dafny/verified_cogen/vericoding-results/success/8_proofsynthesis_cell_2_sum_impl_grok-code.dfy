// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int) returns (sum: int)
    requires 
        a.Length == N &&
        N <= 0x7FFF_FFFF

    ensures
        sum <= 2*N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed unprovable set invariant, replaced with provable s >= 0 && s <= i to ensure sum <= N <= 2*N */
{
  var s := 0;
  if N > 0 {
    for i := 0 to N-1
      invariant 0 <= i <= N
      invariant s >= 0 && s <= i
    {
      if a[i] == 1 {
        s := s + 1;
      }
    }
  }
  sum := s;
}
// </vc-code>
