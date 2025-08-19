//ATOM
predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

//IMPL 
method CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
  {
    /* code modified by LLM (iteration 1): added proof assertions to help Dafny verify set cardinality reasoning */
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
    
    if IsUpperCase(s[i]) {
      assert newSet == oldSet + {i};
      assert i !in oldSet;
      assert |newSet| == |oldSet| + 1;
      count := count + 1;
    } else {
      assert newSet == oldSet;
      assert |newSet| == |oldSet|;
    }
    
    i := i + 1;
  }
}