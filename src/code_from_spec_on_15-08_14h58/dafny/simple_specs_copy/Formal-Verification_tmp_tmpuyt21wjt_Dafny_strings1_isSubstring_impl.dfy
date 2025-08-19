method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  /* code modified by LLM (iteration 1): implement proper logic instead of using assume statements */
  if |pre| > |str| {
    res := false;
    return;
  }
  
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res == (pre[..i] == str[..i])
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): add assertion to help prove postcondition */
  assert pre <= str;
}


//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}


//IMPL 

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
    if |str| < |sub| {
        res := false;
        /* code modified by LLM (iteration 1): added assertion to help prove postcondition when string is too short */
        assert !isSubstringPredicate(sub, str);
        return;
    }
    
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
    {
        var prefixResult := isPrefix(sub, str[i..]);
        if prefixResult {
            res := true;
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when prefix found */
            assert isPrefixPredicate(sub, str[i..]);
            assert isSubstringPredicate(sub, str);
            return;
        }
        i := i + 1;
    }
    
    res := false;
    /* code modified by LLM (iteration 1): fixed bound condition in assertion */
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..]);
    assert !isSubstringPredicate(sub, str);
}