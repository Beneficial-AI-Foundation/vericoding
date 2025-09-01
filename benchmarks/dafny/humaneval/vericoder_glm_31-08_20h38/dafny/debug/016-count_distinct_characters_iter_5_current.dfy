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
import opened Char

function char_at(i: int): char
  requires 0 <= i < 26
  ensures 'a' <= char_at(i) && char_at(i) <= 'z'
{
  chr(ord('a') + i)
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
  count := 0;
  var i := 0;
  while i < 26
    decreases 26 - i
    invariant 0 <= i <= 26
    invariant count == |set j: int | 0 <= j < i && contains_char(s, char_at(j))|
  {
    var c := char_at(i);
    if contains_char(s, c) {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

