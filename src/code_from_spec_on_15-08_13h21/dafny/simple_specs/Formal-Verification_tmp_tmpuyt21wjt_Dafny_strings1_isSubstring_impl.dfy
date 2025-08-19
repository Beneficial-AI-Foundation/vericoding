//ATOM
/* code modified by LLM (iteration 1): replaced assume statements with proper implementation */
method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
    return;
  }
  
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
  
  res := true;
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
        /* code modified by LLM (iteration 1): added assertion to help prove postcondition when string is too short */
        assert !isSubstringPredicate(sub, str);
        res := false;
        return;
    }
    
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
    {
        var prefixRes := isPrefix(sub, str[i..]);
        if prefixRes {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when prefix is found */
            assert isPrefixPredicate(sub, str[i..]);
            assert isSubstringPredicate(sub, str);
            res := true;
            return;
        }
        /* code modified by LLM (iteration 1): added assertion to maintain loop invariant */
        assert !isPrefixPredicate(sub, str[i..]);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition when no prefix is found */
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..]);
    assert !isSubstringPredicate(sub, str);
    res := false;
}