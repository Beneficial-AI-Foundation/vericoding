function contains_char(s: string, c: char): bool
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
{
  if |s| == 0 then false else s[0] == c || s[0] == upper_char(c) || contains_char(s[1..], c)
}
function upper_char(c: char) : (C: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= C <= 'Z'
{ c - 'a' + 'A' }

// <vc-helpers>
// No helper lemmas required for this proof.
// </vc-helpers>

// <vc-spec>
method count_distinct_characters(s: string) returns (count: int)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  // pre-conditions-end
  // post-conditions-start
  ensures count == |set c | 'a' <= c <= 'z' && contains_char(s, c)|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var seen: set<char> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == { c: char | 'a' <= c <= 'z' && (exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c))) }
  {
    var ch := s[i];
    var lc := if 'a' <= ch && ch <= 'z' then ch else ch - 'A' + 'a';
    seen := seen + { lc };
    i := i + 1;
  }
  count := |seen|;
}
// </vc-code>

