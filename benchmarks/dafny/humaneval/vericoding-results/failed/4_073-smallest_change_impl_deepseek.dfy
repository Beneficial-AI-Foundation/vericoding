// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CountRange(s: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |s| / 2
  decreases end - start
{
  if start >= end then 0
  else (if s[start] != s[|s| - 1 - start] then 1 else 0) + CountRange(s, start + 1, end)
}

/* helper modified by LLM (iteration 5): Maintained recursive counting function */
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplified implementation using helper function */
  c := CountRange(s, 0, |s| / 2);
}
// </vc-code>
