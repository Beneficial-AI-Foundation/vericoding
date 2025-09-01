

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
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + (if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0)
{
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
  var ycount := 0;
  var vowels := 0;
  var i := 0;
  var n := |s|;
  
  while i < n
    invariant 0 <= i <= n
    invariant vowels == |(set j | 0 <= j < i && is_vowel(s[j]))|
    invariant ycount == (if i > 0 && isY(s[i-1]) then 1 else 0)
    invariant count == vowels + ycount
  {
    if is_vowel(s[i]) {
      vowels := vowels + 1;
    }
    
    if i > 0 && isY(s[i-1]) {
      ycount := 1;
    } else {
      ycount := 0;
    }
    
    count := vowels + ycount;
    i := i + 1;
  }
  
  // Handle final y check separately
  if n > 0 && isY(s[n-1]) {
    count := count + 1;
  } else {
    // Maintain current count
  }
  
  // Apply lemma to verify postcondition
  CountLemma(s, count, vowels, if n > 0 && isY(s[n-1]) then 1 else 0);
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end