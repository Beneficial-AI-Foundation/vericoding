// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)

  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented binary search with proper invariants for integer cube root */
  var low: nat := 0;
  var high: nat := N + 1;
  while low + 1 < high
    decreases high - low
    invariant 0 <= low <= high <= N + 1
    invariant cube(low) <= N
    invariant N < cube(high)
  {
    var mid: nat := low + (high - low) / 2;
    if cube(mid) <= N
    {
      low := mid;
    }
    else
    {
      high := mid;
    }
  }
  r := low;
}
// </vc-code>
