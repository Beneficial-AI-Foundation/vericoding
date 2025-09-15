// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix recursive function logic */
function CountMismatchesInRange(s: seq<int>, low: int, high: int): int
  requires 0 <= low <= high <= |s|
  ensures CountMismatchesInRange(s, low, high) == |set j | low <= j < high && s[j] != s[|s| - 1 - j]|
  decreases high - low
{
  if low == high then 0 else
  var rest := CountMismatchesInRange(s, low+1, high);
  if low < |s| / 2 && s[low] != s[|s| - 1 - low] then 1 + rest else rest
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix loop invariant */
{
  var count := 0;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant count == CountMismatchesInRange(s, 0, i)
  {
    if s[i] != s[|s| - 1 - i] {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>
