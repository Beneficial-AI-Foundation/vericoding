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
function lower_char(c: char) : (lc: char)
  requires 'A' <= c <= 'Z'
  ensures 'a' <= lc <= 'z'
{ c - 'A' + 'a' }

function normalize_char(c: char) : (nc: char)
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  ensures 'a' <= nc <= 'z'
{
  if 'a' <= c <= 'z' then c else lower_char(c)
}

predicate char_in_string(s: string, c: char)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
{
  exists i :: 0 <= i < |s| && normalize_char(s[i]) == c
}

lemma char_in_string_equiv_contains_char(s: string, c: char)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
  ensures char_in_string(s, c) <==> contains_char(s, c)
{
  if |s| == 0 {
    assert !char_in_string(s, c);
    assert !contains_char(s, c);
  } else {
    if char_in_string(s, c) {
      var i :| 0 <= i < |s| && normalize_char(s[i]) == c;
      if i == 0 {
        if 'a' <= s[0] <= 'z' {
          assert s[0] == c;
          assert contains_char(s, c);
        } else {
          assert s[0] == upper_char(c);
          assert contains_char(s, c);
        }
      } else {
        assert char_in_string(s[1..], c);
        char_in_string_equiv_contains_char(s[1..], c);
        assert contains_char(s[1..], c);
        assert contains_char(s, c);
      }
    }
    if contains_char(s, c) {
      if s[0] == c {
        assert normalize_char(s[0]) == c;
        assert char_in_string(s, c);
      } else if s[0] == upper_char(c) {
        assert normalize_char(s[0]) == c;
        assert char_in_string(s, c);
      } else {
        assert contains_char(s[1..], c);
        char_in_string_equiv_contains_char(s[1..], c);
        assert char_in_string(s[1..], c);
        assert char_in_string(s, c);
      }
    }
  }
}

function string_chars(s: string) : set<char>
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
{
  set i | 0 <= i < |s| :: normalize_char(s[i])
}

lemma string_chars_correct(s: string)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  ensures string_chars(s) == set c | 'a' <= c <= 'z' && contains_char(s, c)
{
  var left := string_chars(s);
  var right := set c | 'a' <= c <= 'z' && contains_char(s, c);
  
  forall c | c in left
    ensures c in right
  {
    var i :| 0 <= i < |s| && c == normalize_char(s[i]);
    assert 'a' <= c <= 'z';
    char_in_string_equiv_contains_char(s, c);
    assert char_in_string(s, c);
    assert contains_char(s, c);
  }
  
  forall c | c in right
    ensures c in left
  {
    assert 'a' <= c <= 'z' && contains_char(s, c);
    char_in_string_equiv_contains_char(s, c);
    assert char_in_string(s, c);
    var i :| 0 <= i < |s| && normalize_char(s[i]) == c;
    assert c in left;
  }
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
  var chars := {};
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant chars == set j | 0 <= j < i :: normalize_char(s[j])
  {
    var normalized := normalize_char(s[i]);
    chars := chars + {normalized};
    i := i + 1;
  }
  
  string_chars_correct(s);
  count := |chars|;
}
// </vc-code>

