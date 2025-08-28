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

lemma contains_char_equiv(s: string, c: char)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
  ensures contains_char(s, c) <==> (exists i :: 0 <= i < |s| && normalize_char(s[i]) == c)
{
  if |s| == 0 {
  } else {
    contains_char_equiv(s[1..], c);
  }
}

lemma set_comprehension_equiv(s: string)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  ensures |set c | 'a' <= c <= 'z' && contains_char(s, c)| == |set i | 0 <= i < |s| :: normalize_char(s[i])|
{
  var char_set := set c | 'a' <= c <= 'z' && contains_char(s, c);
  var norm_set := set i | 0 <= i < |s| :: normalize_char(s[i]);
  
  forall c | c in char_set
    ensures c in norm_set
  {
    contains_char_equiv(s, c);
  }
  
  forall nc | nc in norm_set
    ensures nc in char_set
  {
    var i :| 0 <= i < |s| && nc == normalize_char(s[i]);
    contains_char_equiv(s, nc);
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
  var seen := {};
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == set j | 0 <= j < i :: normalize_char(s[j])
    invariant count == |seen|
    invariant forall c :: c in seen ==> 'a' <= c <= 'z'
  {
    var normalized := normalize_char(s[i]);
    if normalized !in seen {
      seen := seen + {normalized};
      count := count + 1;
    }
    i := i + 1;
  }
  
  set_comprehension_equiv(s);
  assert seen == set j | 0 <= j < |s| :: normalize_char(s[j]);
}
// </vc-code>
