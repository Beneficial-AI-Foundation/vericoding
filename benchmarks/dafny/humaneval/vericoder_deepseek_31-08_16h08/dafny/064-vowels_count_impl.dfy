

// <vc-helpers>
predicate isY(c: char) 
{
  c == 'y' || c == 'Y'
}

lemma CountLemma(s: string, count: int, vowels: int, ycount: int)
  requires 0 <= vowels
  requires 0 <= ycount <= (if |s| > 0 then 1 else 0)
  requires count == vowels + ycount
  requires vowels == |(set i | 0 <= i < |s| && is_vowel(s[i]))|
  requires ycount == (if |s| > 0 && isY(s[|s| - 1]) then 1 else 0)
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + (if |s| > 0 && isY(s[|s| - 1]) then 1 else 0)
{
}

lemma YCountLemma(s: string, i: int)
  requires 0 <= i <= |s|
  ensures (if i > 0 && isY(s[i-1]) then 1 else 0) == (if |s| > 0 && i == |s| && isY(s[|s| - 1]) then 1 else 0)
{
  if i == |s| {
  } else if i > 0 {
    assert i-1 != |s|-1;
  }
}
// </vc-helpers>
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
  var vowels := 0;
  var i := 0;
  var n := |s|;
  var ycount := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant vowels == |(set j | 0 <= j < i && is_vowel(s[j]))|
    invariant ycount == (if i > 0 && isY(s[i-1]) then 1 else 0)
    invariant count == vowels + ycount
  {
    if is_vowel(s[i]) {
      vowels := vowels + 1;
    }
    
    i := i + 1;
    
    if i > 0 {
      if isY(s[i-1]) {
        ycount := 1;
      } else {
        ycount := 0;
      }
    } else {
      ycount := 0;
    }
  }
  
  YCountLemma(s, i);
  count := vowels + ycount;
  
  CountLemma(s, count, vowels, ycount);
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end