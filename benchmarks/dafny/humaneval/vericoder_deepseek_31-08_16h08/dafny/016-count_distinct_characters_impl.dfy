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
lemma contains_char_substring(s: string, c: char, i: int)
  decreases |s|
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 'a' <= c <= 'z'
  requires 0 <= i <= |s|
  ensures contains_char(s[0..i], c) <==> exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c))
{
  if i == 0 {
    // base case: empty substring
  } else {
    // recursive case: check first character and recurse
    contains_char_substring(s[1..], c, i-1);
  }
}

lemma set_equality_lemma(s: string, i: int)
  requires forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z' || 'A' <= s[j] <= 'Z'
  requires 0 <= i <= |s|
  ensures (var A := set c | 'a' <= c <= 'z' && contains_char(s[0..i], c);
           var B := set c | 'a' <= c <= 'z' && exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c));
           A == B)
{
  forall c | 'a' <= c <= 'z'
    ensures contains_char(s[0..i], c) <==> exists j :: 0 <= j < i && (s[j] == c || s[j] == upper_char(c))
  {
    contains_char_substring(s, c, i);
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
    var lower: char;
    if 'a' <= current <= 'z' {
      lower := current;
    } else {
      // Convert uppercase to lowercase
      lower := (current - 'A') + 'a';
    }
    
    if lower !in seen {
      seen := seen + {lower};
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  set_equality_lemma(s, |s|);
}
// </vc-code>

