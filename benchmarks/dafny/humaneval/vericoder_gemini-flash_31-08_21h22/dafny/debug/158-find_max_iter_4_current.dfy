

// <vc-helpers>
function char_set(s: string): set<char>
{
  var charSet: set<char> := {};
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> s[k] in charSet
  {
    charSet := charSet + {s[i]};
    i := i + 1;
  }
  return charSet;
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)
   // pre-conditions-start
    requires |strings| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var max_s := strings[0];
  var i := 1;
  while i < |strings|
    invariant 0 < |strings|
    invariant 0 <= i <= |strings|
    invariant max_s in strings[0..i]
    invariant forall k : int :: 0 <= k < i ==> |char_set(max_s)| >= |char_set(strings[k])|
  {
    if |char_set(strings[i])| > |char_set(max_s)| {
      max_s := strings[i];
    }
    i := i + 1;
  }
  return max_s;
}
// </vc-code>

