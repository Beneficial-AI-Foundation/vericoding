// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added helper function */
function isZ(c: char): bool { c == 'Z' || c == 'z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(text: array<char>) returns (result: bool)
    ensures result == (exists i :: 0 <= i < text.Length && (text[i] == 'Z' || text[i] == 'z'))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants to prove the postcondition */
{
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant forall j :: 0 <= j < i ==> !isZ(text[j])
  {
    if isZ(text[i]) {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
