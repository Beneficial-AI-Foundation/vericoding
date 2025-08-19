/* code modified by LLM (iteration 2): Added IsVowel predicate to resolve unresolved identifier errors */
predicate IsVowel(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

//IMPL 
method CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
  count := 0;
  
  /* code modified by LLM (iteration 1): Added early return for short strings to avoid invariant issues */
  if |s| < 3 {
    return;
  }
  
  var i := 1;
  
  while i < |s| - 1
    /* code modified by LLM (iteration 1): Fixed invariant bounds to handle edge cases properly */
    invariant 1 <= i <= |s| - 1
    invariant count >= 0
    /* code modified by LLM (iteration 3): Added trigger annotation to silence warnings */
    invariant count == | set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
  {
    /* code modified by LLM (iteration 3): Added ghost variables to help prove invariant maintenance */
    ghost var oldSet := set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    ghost var newSet := set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      /* code modified by LLM (iteration 3): Added assertion to help prove set cardinality relationship */
      assert i in newSet;
      assert i !in oldSet;
      assert newSet == oldSet + {i};
      count := count + 1;
    } else {
      /* code modified by LLM (iteration 3): Added assertion for the case when condition is false */
      assert newSet == oldSet;
    }
    i := i + 1;
  }
}