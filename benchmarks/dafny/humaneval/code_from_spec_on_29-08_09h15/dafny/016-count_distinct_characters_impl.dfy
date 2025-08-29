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
lemma distinct_chars_subset(s: string, chars: set<char>)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires chars == set c {:trigger} | 'a' <= c <= 'z' && contains_char(s, c)
  ensures chars <= set c {:trigger} | 'a' <= c <= 'z'
{
}

lemma contains_char_monotonic(s: string, c: char, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i < |s|
  requires contains_char(s[i..], c)
  ensures contains_char(s, c)
  decreases i
{
  if i == 0 {
    assert s[0..] == s;
  } else {
    assert contains_char(s[i..], c);
    contains_char_monotonic(s[1..], c, i - 1);
  }
}

lemma char_case_equivalence(s: string, c: char, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i < |s|
  requires 'A' <= s[i] <= 'Z'
  requires s[i] == upper_char(c)
  ensures contains_char(s, c)
  decreases |s| - i
{
  if |s| > 0 {
    if i == 0 {
      assert s[0] == upper_char(c);
      assert contains_char(s, c);
    } else {
      assert s[1..][i-1] == s[i];
      assert contains_char(s[1..], c);
      assert contains_char(s, c);
    }
  }
}

lemma contains_char_extension(s: string, c: char, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i < |s|
  requires i > 0
  requires contains_char(s[..i], c)
  ensures contains_char(s[..i+1], c)
{
  assert s[..i+1][1..] == s[1..i+1];
  if contains_char(s[..i], c) {
    if s[..i][0] == c || s[..i][0] == upper_char(c) {
      assert s[..i+1][0] == s[0];
      assert s[..i+1][0] == c || s[..i+1][0] == upper_char(c);
    } else {
      assert contains_char(s[..i][1..], c);
      assert s[..i][1..] == s[1..i];
      assert contains_char(s[1..i], c);
      assert contains_char(s[1..i+1], c);
      assert s[..i+1][1..] == s[1..i+1];
      assert contains_char(s[..i+1][1..], c);
    }
  }
}

lemma contains_char_prefix(s: string, c: char, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i < |s|
  requires (s[i] == c || s[i] == upper_char(c))
  ensures contains_char(s[..i+1], c)
{
  if i == 0 {
    assert s[..1][0] == s[0];
    assert s[0] == c || s[0] == upper_char(c);
  } else {
    assert s[..i+1][i] == s[i];
    assert s[i] == c || s[i] == upper_char(c);
    contains_char_at_position(s[..i+1], c, i);
  }
}

lemma contains_char_at_position(s: string, c: char, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i < |s|
  requires s[i] == c || s[i] == upper_char(c)
  ensures contains_char(s[i..], c)
{
  assert s[i..][0] == s[i];
}

lemma contains_char_from_position(s: string, c: char, pos: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= pos < |s|
  requires s[pos] == c || s[pos] == upper_char(c)
  ensures contains_char(s[..pos+1], c)
{
  contains_char_at_position(s, c, pos);
  contains_char_monotonic(s, c, pos);
  assert contains_char(s, c);
  contains_char_prefix_helper(s, c, pos);
}

lemma contains_char_prefix_helper(s: string, c: char, pos: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= pos < |s|
  requires s[pos] == c || s[pos] == upper_char(c)
  ensures contains_char(s[..pos+1], c)
  decreases pos
{
  if pos == 0 {
    assert s[..1][0] == s[0];
  } else {
    if s[0] == c || s[0] == upper_char(c) {
      assert contains_char(s[..pos+1], c);
    } else {
      assert s[pos] == c || s[pos] == upper_char(c);
      contains_char_prefix_helper(s[1..], c, pos - 1);
      assert contains_char(s[1..pos], c);
      assert s[..pos+1][1..] == s[1..pos+1];
      assert contains_char(s[..pos+1][1..], c);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_distinct_characters(string: str) -> int
Given a string, find out how many distinct characters (regardless of case) does it consist of
*/
// </vc-description>

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
  var checked: set<char> := {};
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant checked <= set c {:trigger} | 'a' <= c <= 'z'
    invariant count == |checked|
    invariant checked == set c {:trigger} | 'a' <= c <= 'z' && contains_char(s[..i], c)
  {
    var ch := s[i];
    var lower_ch: char;
    
    if 'a' <= ch <= 'z' {
      lower_ch := ch;
    } else {
      lower_ch := ch - 'A' + 'a';
    }
    
    contains_char_from_position(s, lower_ch, i);
    
    if lower_ch !in checked {
      checked := checked + {lower_ch};
      count := count + 1;
    }
    
    forall c | 'a' <= c <= 'z' && contains_char(s[..i], c)
      ensures contains_char(s[..i+1], c)
    {
      if i > 0 {
        contains_char_extension(s, c, i);
      } else {
        assert s[..0] == "";
        assert !contains_char("", c);
        assert false;
      }
    }
  }
  
  assert s[..|s|] == s;
}
// </vc-code>

