//ATOM
predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

//IMPL 
method CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
  count := 0;
  
  /* code modified by LLM (iteration 3): Added bounds check to handle edge cases where string length < 3 */
  if |s| < 3 {
    return;
  }
  
  var i := 1;
  
  /* code modified by LLM (iteration 3): Fixed loop invariant to properly handle bounds and maintain correctness */
  while i < |s| - 1
    invariant 1 <= i <= |s| - 1
    invariant count >= 0
    invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
  {
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 3): Added assertion to establish postcondition from loop invariant */
  assert i == |s| - 1;
  assert count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |;
  assert i == |s| - 1;
  assert (set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])) == (set j: int | 1 <= j < |s| - 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]));
}