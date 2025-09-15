// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement loop to count mismatches */
  var len := |s| / 2;
  c := 0;
  for i := 0 to len - 1 {
    if s[i] != s[|s| - 1 - i] {
      c := c + 1;
    }
  }
}
// </vc-code>
