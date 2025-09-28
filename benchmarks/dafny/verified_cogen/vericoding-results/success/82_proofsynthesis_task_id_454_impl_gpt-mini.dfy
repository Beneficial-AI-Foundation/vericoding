// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): character check for Z or z */
predicate IsZ(c: char) { c == 'Z' || c == 'z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): scan array for Z or z using IsZ predicate */
  var i := 0;
  result := false;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant result == (exists j :: 0 <= j < i && IsZ(text[j]))
  {
    if IsZ(text[i]) {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
