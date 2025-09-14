predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 1;
  while i < |s| - 1
    invariant 1 <= i
    invariant count == | set j: int | 1 <= j < i && j + 1 < |s| && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    decreases |s| - i
  {
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      count := count + 1;
    }
    i := i + 1;
  }
  assert i >= |s| - 1;
  assert (set j: int | 1 <= j < i && j + 1 < |s| && IsVowel(s[j-1]) && IsVowel(s[j+1])) ==
         (set j: int | 1 <= j < |s| - 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]));
}
// </vc-code>

