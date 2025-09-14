// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize result before loop and set it to false after the loop if no 'z' or 'Z' is found */
{
  var i := 0;
  var result_found := false;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result_found <==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'))
  {
    if s[i] == 'z' || s[i] == 'Z' {
      result_found := true;
      break;
    }
    i := i + 1;
  }
  result := result_found;
}
// </vc-code>
