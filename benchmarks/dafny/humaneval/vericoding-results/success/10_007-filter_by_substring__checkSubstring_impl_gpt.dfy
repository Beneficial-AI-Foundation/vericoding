// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retain simple min utility; no complex lemmas needed */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement straightforward substring search with simple decreasing measures and early return */
  var n := |s|;
  var m := |sub|;
  if m == 0 {
    result := true;
    return;
  }
  if m > n {
    result := false;
    return;
  }
  var i := 0;
  while i <= n - m
    invariant 0 <= i <= n - m + 1
    decreases n - i
  {
    var j := 0;
    while j < m
      invariant 0 <= i <= n - m
      invariant 0 <= j <= m
      invariant j < m ==> i + j < n
      decreases m - j
    {
      if s[i + j] == sub[j] {
        j := j + 1;
      } else {
        j := m;
      }
    }
    if j == m {
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
