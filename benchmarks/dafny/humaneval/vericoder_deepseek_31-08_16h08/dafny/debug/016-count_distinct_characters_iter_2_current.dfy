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
lemma {:induction s} contains_char_lemma(s: string, c: char, d: char)
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 'a' <= d <= 'z'
  ensures contains_char(s, c) && contains_char(s, d) && c == d ==> c == d
{
}

ghost function count_distinct_in_set(s: set<char>): int
  decreases s
{
  if s == {} then 0 else
    var c :| c in s;
    1 + count_distinct_in_set(s - {c})
}

lemma contains_char_substring(s: string, c: char, i: int)
  decreases |s|
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i <= |s|
  ensures contains_char(s[0..i], c) <==> contains_char(s, c) && exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c))
{
}

lemma set_equality_lemma(s: string, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 0 <= i <= |s|
  ensures set c | 'a' <= c <= 'z' && contains_char(s[0..i], c) == set c | 'a' <= c <= 'z' && exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c))
{
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
  var seen: set<char> := {};
  var i: int := 0;
  count := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall c :: c in seen ==> 'a' <= c <= 'z' && contains_char(s[0..i], c)
    invariant seen == set c | 'a' <= c <= 'z' && contains_char(s[0..i], c)
    invariant count == |seen|
  {
    var current: char := s[i];
    var lower: char :| 'a' <= lower <= 'z' && (current == lower || current == upper_char(lower));
    
    if lower !in seen {
      seen := seen + {lower};
      count := count + 1;
    }
    
    i := i + 1;
    
    // Update invariants for the new substring
    assert forall c :: c in seen ==> 'a' <= c <= 'z' && contains_char(s[0..i], c);
    assert seen == set c | 'a' <= c <= 'z' && contains_char(s[0..i], c);
  }
  
  // Final proof that the set equals the required set
  assert forall c :: 'a' <= c <= 'z' ==> (contains_char(s, c) == contains_char(s[0..|s|], c));
  assert set c | 'a' <= c <= 'z' && contains_char(s, c) == set c | 'a' <= c <= 'z' && contains_char(s[0..|s|], c);
}
// </vc-code>

