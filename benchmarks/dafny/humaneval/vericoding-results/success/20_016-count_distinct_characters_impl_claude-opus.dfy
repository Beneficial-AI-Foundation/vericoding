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
lemma set_cardinality_helper(s: string, c: char, seen: set<char>)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
  requires seen == set ch | 'a' <= ch < c && contains_char(s, ch)
  ensures c !in seen
{
  if c in seen {
    assert 'a' <= c < c;
    assert false;
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
  count := 0;
  var c: char := 'a';
  ghost var seen: set<char> := {};
  
  while c <= 'z'
    invariant 'a' <= c <= ('z' as int + 1) as char
    invariant seen == set ch | 'a' <= ch < c && contains_char(s, ch)
    invariant count == |seen|
  {
    if contains_char(s, c) {
      set_cardinality_helper(s, c, seen);
      seen := seen + {c};
      count := count + 1;
    }
    c := (c as int + 1) as char;
  }
  
  assert c == ('z' as int + 1) as char;
  assert seen == set ch | 'a' <= ch <= 'z' && contains_char(s, ch);
}
// </vc-code>

