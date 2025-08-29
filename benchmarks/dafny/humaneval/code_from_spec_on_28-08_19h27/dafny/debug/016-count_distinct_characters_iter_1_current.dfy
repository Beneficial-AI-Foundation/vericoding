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
function to_lower_char(c: char): char
  requires 'A' <= c <= 'Z' || 'a' <= c <= 'z'
{
  if 'A' <= c <= 'Z' then c - 'A' + 'a' else c
}

function normalize_char(c: char): char
  requires 'A' <= c <= 'Z' || 'a' <= c <= 'z'
{
  to_lower_char(c)
}

function collect_normalized_chars(s: string, i: int): set<char>
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  decreases |s| - i
{
  if i >= |s| then {}
  else {normalize_char(s[i])} + collect_normalized_chars(s, i + 1)
}

lemma collect_normalized_chars_complete(s: string, i: int)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  ensures collect_normalized_chars(s, i) == collect_normalized_chars(s, 0) - collect_normalized_chars(s, 0) + collect_normalized_chars(s, i)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_distinct_characters(string: str) -> int
Given a string, find out how many distinct characters (regardless of case) does it consist of
*/
// </vc-description>

// <vc-spec>
function count_distinct_characters(s: string): int
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  ensures count_distinct_characters(s) >= 0
  ensures count_distinct_characters(s) <= 26
// </vc-spec>
// <vc-code>
{
  |collect_normalized_chars(s, 0)|
}
// </vc-code>
