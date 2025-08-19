predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

//IMPL 
method CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  /* code modified by LLM (iteration 1): Added explicit trigger to eliminate warning */
  ensures count == | set i: int {:trigger IsVowel(s[i-1]), IsVowel(s[i+1])} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
  count := 0;
  
  /* code modified by LLM (iteration 2): Added early return for strings too short to have vowel neighbors */
  if |s| <= 2 {
    return;
  }
  
  var i := 1;
  
  /* code modified by LLM (iteration 2): Fixed loop invariant to properly track the relationship between count and set cardinality */
  while i < |s| - 1
    invariant 1 <= i <= |s| - 1
    invariant count >= 0
    invariant count == | set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
  {
    /* code modified by LLM (iteration 2): Added assertion to help Dafny understand the set relationship */
    var oldCount := count;
    var oldSet := set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
      count := count + 1;
      
      /* code modified by LLM (iteration 2): Assert that adding current index increases set size by 1 */
      var newSet := set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i+1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
      assert i in newSet;
      assert i !in oldSet;
      assert newSet == oldSet + {i};
      assert |newSet| == |oldSet| + 1;
    } else {
      /* code modified by LLM (iteration 2): Assert that not adding current index keeps set size same */
      var newSet := set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i+1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
      assert i !in newSet;
      assert newSet == oldSet;
      assert |newSet| == |oldSet|;
    }
    
    i := i + 1;
  }
}