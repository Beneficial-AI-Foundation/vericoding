predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL 
method CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && IsDigit(s[j])|
  {
    /* code modified by LLM (iteration 1): Added ghost variables and assertions to help Dafny prove the invariant is maintained */
    ghost var oldSet := set j: int | 0 <= j < i && IsDigit(s[j]);
    ghost var newSet := set j: int | 0 <= j < i + 1 && IsDigit(s[j]);
    
    if IsDigit(s[i]) {
      /* code modified by LLM (iteration 1): Assert that the new set equals the old set union with the current index */
      assert newSet == oldSet + {i};
      assert |newSet| == |oldSet| + 1;
      count := count + 1;
    } else {
      /* code modified by LLM (iteration 1): Assert that the sets are equal when current character is not a digit */
      assert newSet == oldSet;
      assert |newSet| == |oldSet|;
    }
    i := i + 1;
  }
}