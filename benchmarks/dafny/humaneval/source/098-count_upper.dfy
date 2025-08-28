method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
{
  // impl-start
  ghost var found := {};
  cnt := 0;
  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant cnt == |found|
    invariant found == set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])
    // invariants-end
  {
    if is_upper_vowel(s[i]) && i % 2 == 0 {
      cnt := cnt + 1;
      found := found + {i};
    }
    i := i + 1;
  }
  // impl-end
}

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end
