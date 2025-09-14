// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add IsZ and safe HasZPrefix with length bound */
predicate IsZ(c: char) { c == 'z' || c == 'Z' }
predicate HasZPrefix(s: string, n: int) { 0 <= n <= |s| && exists i :: 0 <= i < n && IsZ(s[i]) }
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate through string to determine if it contains 'z' or 'Z' */
  var i := 0;
  var found := false;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant found <==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'))
    decreases |s| - i
  {
    if s[i] == 'z' || s[i] == 'Z' {
      found := true;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>
