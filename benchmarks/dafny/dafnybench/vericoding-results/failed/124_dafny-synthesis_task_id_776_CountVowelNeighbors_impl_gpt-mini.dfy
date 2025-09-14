predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
// No helper declarations needed.
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n < 3 {
    count := 0;
    return;
  }
  count := 0;
  var i := 1;
  ghost var S: set<int> := {};
  while i < n-1
    invariant 1 <= i <= n-1
    invariant count == |S|
    invariant S == set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])
    decreases n - i
  {
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      S := S + {i};
    }
    count := |S|;
    i := i + 1;
  }
}
// </vc-code>

