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
function method IsLowercase(c: char): bool { 'a' <= c <= 'z' }
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
  var distinct_chars := set{};
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant forall c :: c in distinct_chars ==> IsLowercase(c)
    invariant forall c :: c in distinct_chars ==> contains_char(s[0..i], c)
  {
    if IsLowercase(s[i]) {
      distinct_chars := distinct_chars + {s[i]};
    } else {
      distinct_chars := distinct_chars + {s[i] + 'a' - 'A'};
    }
  }
  count := |distinct_chars|;
}
// </vc-code>

