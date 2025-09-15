// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add explicit trigger to fix quantifier warning */
function Contains(str: string, substr: string): bool
{
  |substr| <= |str| && exists i {:trigger str[i..i+|substr|]} :: 0 <= i <= |str| - |substr| && str[i..i+|substr|] == substr
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)

    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fix compilation error by using Contains helper instead of 'in' operator */
{
  res := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |res| <= i
    invariant forall s :: s in res ==> s in strings
  {
    if Contains(strings[i], substring) {
      res := res + [strings[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
