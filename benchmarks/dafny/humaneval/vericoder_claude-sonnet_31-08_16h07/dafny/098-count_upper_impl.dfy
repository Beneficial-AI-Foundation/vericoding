

// <vc-helpers>
lemma CountUpperCorrectness(s: string, cnt: int, i: int)
  requires 0 <= i < |s|
  requires cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
  ensures cnt + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0) == 
          |set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j])|
{
  var old_set := set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j]);
  var new_set := set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j]);
  
  if i % 2 == 0 && is_upper_vowel(s[i]) {
    assert new_set == old_set + {i};
    assert i !in old_set;
    assert |new_set| == |old_set| + 1;
  } else {
    assert new_set == old_set;
  }
}
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
  {
    CountUpperCorrectness(s, cnt, i);
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end