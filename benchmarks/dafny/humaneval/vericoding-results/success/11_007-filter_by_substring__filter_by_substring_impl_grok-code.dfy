// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: string, sub: string): bool
decreases |s|
{
  if |sub| > |s| then false
  else if |sub| == 0 then true
  else if s[0..|sub|] == sub then true
  else Contains(s[1..], sub)
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)

    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): added loop invariants to ensure postconditions are maintained and provable */
  var result: seq<string> := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |result| <= i
    invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && result[k] == strings[j]
  {
    if Contains(strings[i], substring) {
      result := result + [strings[i]];
    }
    i := i + 1;
  }
  res := result;
}
// </vc-code>
