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
function lower_char(c: char) : (C: char)
  requires ('a' <= c <= 'z') || ('A' <= c <= 'Z')
  ensures 'a' <= C <= 'z'
{
  if 'a' <= c <= 'z' then c else c - 'A' + 'a'
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
  var present := new bool[26];
  var i := 0;
  while i < |s|
  {
    var idx: int := lower_char(s[i]) - 'a';
    present[idx] := true;
    i := i + 1;
  }
  count := 0;
  i := 0;
  while i < 26
  {
    if present[i] { count := count + 1; }
    i := i + 1;
  }
}
// </vc-code>

