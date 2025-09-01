

// <vc-helpers>
lemma SeenIsVowelSet(s: string, seen: set<int>)
  requires forall j :: j in seen ==> 0 <= j < |s| && is_vowel(s[j])
  requires forall j :: 0 <= j < |s| && is_vowel(s[j]) ==> j in seen
  ensures seen == (set i | 0 <= i < |s| && is_vowel(s[i]))
{
  // From the two implications we get the equivalence for all elements,
  // which entails set equality by extensionality.
  assert forall k :: k in seen <==> 0 <= k < |s| && is_vowel(s[k]);
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  ghost var seen: set<int> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: j in seen ==> 0 <= j < i && is_vowel(s[j])
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> j in seen
    invariant count == |seen|
  {
    if is_vowel(s[i]) {
      seen := seen + {i};
      count := count + 1;
    }
    i := i + 1;
  }
  // At loop exit i == |s|, so the invariants cover the whole string
  call SeenIsVowelSet(s, seen);
  assert count == |(set i | 0 <= i < |s| && is_vowel(s[i]))|;
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end