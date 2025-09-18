// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ContainsZHelper(s: string, idx: int): bool
  requires 0 <= idx <= |s|
  ensures ContainsZHelper(s, idx) <==> exists i :: idx <= i < |s| && IsZ(s[i])
  decreases |s| - idx
{
  if idx == |s| then
    false
  else
    IsZ(s[idx]) || ContainsZHelper(s, idx + 1)
}
predicate IsZ(c: char) { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed termination error in helper */
  result := ContainsZHelper(s, 0);
}
// </vc-code>
