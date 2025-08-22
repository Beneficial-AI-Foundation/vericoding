//ATOM
method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  /* code modified by LLM (iteration 1): implemented proper prefix checking logic */
  if |pre| > |str| {
    res := false;
    return;
  }
  
  if |pre| == 0 {
    res := true;
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
 |str| >= |sub| && (exists i :: 0 <= i <= |str| - |sub| && isPrefixPredicate(sub, str[i..]))
}

//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}

//IMPL isSubstring
method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  if |str| < |sub| {
    res := false;
    return;
  }
  
  /* code modified by LLM (iteration 1): fixed loop bounds and added proper invariants */
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
  {
    var prefixRes := isPrefix(sub, str[i..]);
    if prefixRes {
      res := true;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): ensured correct final result */
  res := false;
}