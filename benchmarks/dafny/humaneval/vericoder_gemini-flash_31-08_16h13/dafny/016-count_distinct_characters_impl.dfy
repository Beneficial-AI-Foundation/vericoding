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
function upper_char_helper(c: char) : (C: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= C <= 'Z'
{ (c as int - 'a' as int + 'A' as int) as char }

function contains_char_helper(s: string, c: char): bool
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> (('a' <= s[i] <= 'z') || ('A' <= s[i] <= 'Z'))
  requires 'a' <= c <= 'z'
{
  if |s| == 0 then false else s[0] == c || s[0] == upper_char_helper(c) || contains_char_helper(s[1..], c)
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
  var c_val := 'a';
  while c_val <= 'z'
    invariant 'a' <= c_val <= 'z' || c_val == ('z' as int + 1) as char
    invariant forall ch :: 'a' <= ch < c_val ==> (ch in distinct_chars <==> contains_char_helper(s, ch))
    invariant forall ch :: ch in distinct_chars ==> 'a' <= ch <= 'z'
    invariant forall ch :: ch in distinct_chars ==> contains_char_helper(s,ch)
    invariant forall ch :: 'a' <= ch < c_val && contains_char(s, ch) ==> ch in distinct_chars
  {
    if contains_char_helper(s, c_val) {
      distinct_chars := distinct_chars + {c_val};
    }
    c_val := (c_val as int + 1) as char;
  }
  count := |distinct_chars|;
}
// </vc-code>

