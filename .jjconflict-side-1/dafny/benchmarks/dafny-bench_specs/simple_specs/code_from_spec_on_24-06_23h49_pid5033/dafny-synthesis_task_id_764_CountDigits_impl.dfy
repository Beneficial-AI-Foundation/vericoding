//ATOM
predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

//IMPL CountDigits
method CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  count := 0;
  var j := 0;
  
  while j < |s|
    invariant 0 <= j <= |s|
    invariant count >= 0
    invariant count == | set i: int | 0 <= i < j && IsDigit(s[i])|
  {
    if IsDigit(s[j]) {
      /* code modified by LLM (iteration 1): Added assertions to help Dafny prove set cardinality reasoning */
      var oldSet := set i: int | 0 <= i < j && IsDigit(s[i]);
      var newSet := set i: int | 0 <= i < j + 1 && IsDigit(s[i]);
      
      assert j !in oldSet;
      assert newSet == oldSet + {j};
      assert |newSet| == |oldSet| + 1;
      
      count := count + 1;
    } else {
      /* code modified by LLM (iteration 1): Added assertion for the case when character is not a digit */
      assert (set i: int | 0 <= i < j + 1 && IsDigit(s[i])) == (set i: int | 0 <= i < j && IsDigit(s[i]));
    }
    j := j + 1;
  }
}