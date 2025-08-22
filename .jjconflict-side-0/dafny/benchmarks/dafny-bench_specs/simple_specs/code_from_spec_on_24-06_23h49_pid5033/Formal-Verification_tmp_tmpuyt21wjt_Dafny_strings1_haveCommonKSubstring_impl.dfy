//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  res := false;
  assume res ==> isSubstringPredicate(sub, str);
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  res := false;
  assume |pre| > |str| ==> !res;
  assume res ==> isPrefixPredicate(pre, str);
  return res;
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
  
  /* code modified by LLM (iteration 3): fixed loop invariants to match loop condition */
  while i <= |str1| - k && !found
    invariant 0 <= i <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
    invariant found ==> exists j :: 0 <= j < i && isSubstringPredicate((str1[j..])[..k], str2)
  {
    var substring := (str1[i..])[..k];
    var isSubstr := isSubstring(substring, str2);
    
    if isSubstr {
      found := true;
      /* code modified by LLM (iteration 3): added assertion to help verification */
      assert isSubstringPredicate((str1[i..])[..k], str2);
      assert haveCommonKSubstringPredicate(k, str1, str2);
    } else {
      i := i + 1;
    }
  }
  
  /* code modified by LLM (iteration 3): corrected final assertion range */
  if !found {
    assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPredicate((str1[j..])[..k], str2);
    assert !haveCommonKSubstringPredicate(k, str1, str2);
  }
}