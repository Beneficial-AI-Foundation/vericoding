

// <vc-helpers>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}

lemma set_cardinality<T>(s: set<T>, l: seq<T>)
  requires s == set l
  ensures |s| == |l| - (multiset(l)[l[0]] - 1)
{
  var t := set l;
  calc {
    |s|;
    { assert t == s; }
    |t|;
    |multiset(l).Keys|;
  }
}

lemma set_builder_equivalence<T>(s: seq<T>, p: T->bool)
  ensures |set i | 0 <= i < |s| && p(s[i])| == |multiset(i | 0 <= i < |s| && p(s[i])).Keys|
{
  var indexSet := set i | 0 <= i < |s| && p(s[i]);
  var filteredMultiset := multiset(i | 0 <= i < |s| && p(s[i]));
  assert indexSet == filteredMultiset.Keys;
  assert |indexSet| == |filteredMultiset.Keys|;
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
  cnt := |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|;
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end