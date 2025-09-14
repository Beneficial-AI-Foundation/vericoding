// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger to exists quantifier to resolve compilation warning. */
predicate IsSubstring(sub: string, s: string)
{
  exists i :: 0 <= i <= |s| - |sub| && {:trigger s[i..i+|sub|]} s[i..i+|sub|] == sub
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)

    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no logic change needed, as the error was a compilation warning in the helper. */
{
  res := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |res| <= i
    invariant forall s :: s in res ==> s in strings
    invariant forall s :: s in res ==> IsSubstring(substring, s)
  {
    if IsSubstring(substring, strings[i]) {
      res := res + [strings[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
