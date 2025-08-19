//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  /* code modified by LLM (iteration 1): implemented proper substring checking instead of assume statements */
  if |sub| > |str| {
    res := false;
    return;
  }
  
  res := false;
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
  {
    var isPrefix := isPrefixCheck(sub, str[i..]);
    if isPrefix {
      res := true;
      return;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 1): added helper method for prefix checking */
method isPrefixCheck(pre: string, str: string) returns (res: bool)
ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
    return;
  }
  
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res ==> forall j :: 0 <= j < i ==> pre[j] == str[j]
    invariant !res ==> exists j :: 0 <= j < i && pre[j] != str[j]
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
}


//ATOM

method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  /* code modified by LLM (iteration 1): implemented proper prefix checking instead of assume statements */
  if |pre| > |str| {
    res := false;
    return;
  }
  
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res ==> forall j :: 0 <= j < i ==> pre[j] == str[j]
    invariant !res ==> exists j :: 0 <= j < i && pre[j] != str[j]
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
}


//ATOM

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
 ensures |str1| < k || |str2| < k ==> !found
 ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
  if |str1| < k || |str2| < k {
    found := false;
    return;
  }
  
  found := false;
  var i := 0;
  
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
    invariant found ==> haveCommonKSubstringPredicate(k, str1, str2)
  {
    var substr := (str1[i..])[..k];
    var isSubstr := isSubstring(substr, str2);
    
    if isSubstr {
      found := true;
      return;
    }
    
    i := i + 1;
  }
}