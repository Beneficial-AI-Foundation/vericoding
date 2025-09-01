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
function upper_char(c: char) : (C: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= C <= 'Z'
{ c - 'a' + 'A' }

function contains_char(s: string, c: char): bool
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
{
  if |s| == 0 then false else s[0] == c || s[0] == upper_char(c) || contains_char(s[1..], c)
}
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
  var distinct_chars := {};
  for c := 'a' to 'z' {
    if contains_char(s, c) {
      distinct_chars := distinct_chars + {c};
    }
  }
  count := |distinct_chars|;
}
// </vc-code>

