

// <vc-helpers>
lemma VowelCountSet(s: string, n: int)
  requires 0 <= n <= |s|
  ensures |set i | 0 <= i < n && is_vowel(s[i])| == VowelCountHelper(s, n)
  decreases n
{
  if n == 0 {
    assert (set i | 0 <= i < 0 && is_vowel(s[i])) == {};
  } else {
    VowelCountSet(s, n - 1);
    var prevSet := set i | 0 <= i < n - 1 && is_vowel(s[i]);
    var currSet := set i | 0 <= i < n && is_vowel(s[i]);
    
    if is_vowel(s[n - 1]) {
      assert currSet == prevSet + {n - 1};
    } else {
      assert currSet == prevSet;
    }
  }
}

function VowelCountHelper(s: string, n: int): int
  requires 0 <= n <= |s|
  decreases n
{
  if n == 0 then 0
  else VowelCountHelper(s, n - 1) + (if is_vowel(s[n - 1]) then 1 else 0)
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
  var vowels := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant vowels == VowelCountHelper(s, i)
  {
    if is_vowel(s[i]) {
      vowels := vowels + 1;
    }
    i := i + 1;
  }
  
  VowelCountSet(s, |s|);
  
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := vowels + 1;
  } else {
    count := vowels;
  }
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end