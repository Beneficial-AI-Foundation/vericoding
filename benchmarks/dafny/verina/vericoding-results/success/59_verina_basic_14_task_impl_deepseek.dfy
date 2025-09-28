// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isZ(c: char): bool { c == 'z' || c == 'Z' }
function containsZ(s: string, index: int): bool
  requires 0 <= index <= |s|
  ensures containsZ(s, index) <==> exists i :: index <= i < |s| && isZ(s[i])
  decreases |s| - index
{
  if index == |s| then
    false
  else
    if isZ(s[index]) then
      true
    else
      containsZ(s, index + 1)
}
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added termination clause to helper function */
  result := containsZ(s, 0);
}
// </vc-code>
