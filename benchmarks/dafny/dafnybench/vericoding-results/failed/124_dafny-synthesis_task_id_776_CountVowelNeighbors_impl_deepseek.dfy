predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

lemma CountVowelNeighborsLemma(s: string, i: int)
  requires 1 <= i < |s| - 1
  ensures IsVowel(s[i-1]) && IsVowel(s[i+1]) <==> 
          (i in set k: int | 1 <= k < |s|-1 && IsVowel(s[k-1]) && IsVowel(s[k+1]))
{
}

function CountVowelHelper(s: string, n: int): (c: int)
  requires 0 <= n <= |s|
  ensures c == | set k: int | 1 <= k < n && IsVowel(s[k-1]) && IsVowel(s[k+1]) |
{
  if n <= 1 then
    0
  else
    var prev := CountVowelHelper(s, n-1);
    if n-1 >= 1 && n < |s| && IsVowel(s[n-2]) && IsVowel(s[n]) then
      prev + 1
    else
      prev
}

lemma SetComprehensionProperty(s: string)
  ensures | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) | == CountVowelHelper(s, |s|-1)
{
  if |s| <= 2 {
  } else {
    SetComprehensionProperty(s[0..|s|-1]);
  }
}
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i: int := 1;
  while i < |s| - 1
    invariant 1 <= i <= |s|
    invariant count == CountVowelHelper(s, i)
  {
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      count := count + 1;
    }
    i := i + 1;
  }
  assert CountVowelHelper(s, |s|-1) == CountVowelHelper(s, i);
}
// </vc-code>

