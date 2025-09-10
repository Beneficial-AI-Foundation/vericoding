

// <vc-helpers>
lemma SetExtensionality(s: string, k: int, cnt: int)
  requires 0 <= k < |s|
  requires cnt == |set i | 0 <= i < k && i % 2 == 0 && is_upper_vowel(s[i])|
  ensures k % 2 == 0 && is_upper_vowel(s[k]) ==>
    |set i | 0 <= i < k + 1 && i % 2 == 0 && is_upper_vowel(s[i])| == cnt + 1
  ensures k % 2 != 0 || !is_upper_vowel(s[k]) ==>
    |set i | 0 <= i < k + 1 && i % 2 == 0 && is_upper_vowel(s[i])| == cnt
{
  var S_k := set i | 0 <= i < k && i % 2 == 0 && is_upper_vowel(s[i]);
  var S_k1 := set i | 0 <= i < k + 1 && i % 2 == 0 && is_upper_vowel(s[i]);
  
  if k % 2 == 0 && is_upper_vowel(s[k]) {
    assert S_k1 == S_k + {k};
    assert k !in S_k;
    assert |S_k1| == |S_k| + 1;
  } else {
    assert S_k1 == S_k;
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
  var k := 0;
  var counted := {};
  
  while k < |s|
    invariant 0 <= k <= |s|
    invariant counted == set i | 0 <= i < k && i % 2 == 0 && is_upper_vowel(s[i])
    invariant cnt == |counted|
  {
    var old_cnt := cnt;
    if k % 2 == 0 && is_upper_vowel(s[k]) {
      counted := counted + {k};
      cnt := cnt + 1;
    }
    SetExtensionality(s, k, old_cnt);
    k := k + 1;
  }
  
  assert counted == set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i]);
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end