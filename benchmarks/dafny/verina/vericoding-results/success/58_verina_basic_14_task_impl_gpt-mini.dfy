// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate to check if a character is 'z' or 'Z' */
function IsZ(c: char): bool { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate over string to detect 'z' or 'Z' without warnings */
  var i := 0;
  result := false;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && IsZ(s[j])
    decreases |s| - i
  {
    if IsZ(s[i]) {
      result := true;
      i := |s|;
    } else {
      i := i + 1;
    }
  }
}
// </vc-code>
