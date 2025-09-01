

// <vc-helpers>
lemma count_set_succ(s: string, i: int)
  requires 0 <= i < |s|
  ensures |set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])| ==
          |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0)
{
  var A := set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j]);
  if i % 2 == 0 && is_upper_vowel(s[i]) {
    // show the sets differ exactly by the element i
    assert (set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])) == A + (set k | k == i);
    // i is not in A because elements of A are < i
    assert forall k :: k in A ==> k != i;
    // therefore the cardinality increases by 1
    assert |A + (set k | k == i)| == |A| + 1;
    calc {
      |set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])|;
      == |A + (set k | k == i)|;
      == |A| + 1;
      == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + 1;
      == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0);
    }
  } else {
    // if P(i) does not hold, the set doesn't change
    assert (set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])) == A;
    calc {
      |set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])|;
      == |A|;
      == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|;
      == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0);
    }
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
  var i := 0;
  cnt := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|;
    decreases |s| - i;
  {
    var prevCnt := cnt;
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
    }
    // use lemma to relate counts for i and i+1
    count_set_succ(s, i);
    // combine previous invariant and lemma to establish invariant for i+1
    assert cnt == prevCnt + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0);
    assert |set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])| ==
           |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + (if i % 2 == 0 && is_upper_vowel(s[i]) then 1 else 0);
    assert cnt == |set j | 0 <= j < i+1 && j % 2 == 0 && is_upper_vowel(s[j])|;
    i := i + 1;
  }
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end