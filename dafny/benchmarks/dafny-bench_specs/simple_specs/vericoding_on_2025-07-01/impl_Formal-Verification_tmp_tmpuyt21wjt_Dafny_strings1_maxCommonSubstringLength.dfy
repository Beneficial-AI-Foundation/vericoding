//ATOM

predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
  forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

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

predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}

//ATOM

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}

//ATOM

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
 ensures |str1| < k || |str2| < k ==> !found
 ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
  found := false;
  assume |str1| < k || |str2| < k ==> !found;
  assume haveCommonKSubstringPredicate(k,str1,str2) ==> found;
  return found;
}


// SPEC

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
}