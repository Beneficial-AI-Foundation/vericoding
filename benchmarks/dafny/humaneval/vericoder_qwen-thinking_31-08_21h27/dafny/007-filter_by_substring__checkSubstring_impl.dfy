

// <vc-helpers>
function isSubstring(s: string, sub: string) : bool
  decreases |s|
{
  if sub == "" then true
  else if |s| < |sub| then false
  else if s[0] == sub[0] then isSubstring(s[1..], sub[1..])
  else isSubstring(s[1..], sub)
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{ return isSubstring(s, sub); }
// </vc-code>

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
  assume{:axiom} false;
}