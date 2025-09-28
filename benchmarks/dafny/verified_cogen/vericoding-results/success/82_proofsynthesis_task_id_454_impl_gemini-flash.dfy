// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no changes */
// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize result and fix loop invariant proof on entry */
{
  var i := 0;
  result := false;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant result == (exists k :: 0 <= k < i && (text[k] == 'Z' || text[k] == 'z'))
  {
    if text[i] == 'Z' || text[i] == 'z' {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
