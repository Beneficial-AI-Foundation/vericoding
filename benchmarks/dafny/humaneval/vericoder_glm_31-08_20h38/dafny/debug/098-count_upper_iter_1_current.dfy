

// <vc-helpers>
lemma set_cardinality<T>(s: set<T>, l: seq<T>)
  requires s == multiset(l).Keys
  ensures |s| == |l| - (multiset(l)[l[0]] - 1)
{
  calc {
    |s|;
    { assert multiset(l).Keys == s; }
    |multiset(l).Keys|;
    { assert |multiset(l)| == |l|; }
    |multiset(l).Keys|;
  }
}

lemma set_builder_equivalence<T>(s: seq<T>, p: T->bool)
  ensures |set i | 0 <= i < |s| && p(s[i])| == |multiset(i | 0 <= i < |s| && p(s[i])).Keys|
{
  var indexes :== multiset(i | 0 <= i < |s| && p(s[i]));
  var filtered :== set i | 0 <= i < |s| && p(s[i]);
  assert filtered == indexes.Keys;
  assert |filtered| == |indexes.Keys|;
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
  var m: multiset<char> := multiset(c | c in s && is_upper_vowel(c));
  cnt := |m.Keys|;
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end