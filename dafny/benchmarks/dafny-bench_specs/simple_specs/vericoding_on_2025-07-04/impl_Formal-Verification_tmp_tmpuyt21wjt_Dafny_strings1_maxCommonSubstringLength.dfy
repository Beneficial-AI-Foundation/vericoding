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

//IMPL 

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  len := 0;
  
  var k := maxLen;
  /* code modified by LLM (iteration 1): Fixed loop to search from maximum down to find the largest common substring */
  while k > len
    invariant 0 <= len <= k <= maxLen
    invariant len <= |str1| && len <= |str2|
    invariant forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
    invariant len == 0 || haveCommonKSubstringPredicate(len, str1, str2)
  {
    var found := haveCommonKSubstring(k, str1, str2);
    if found {
      len := k;
      break;
    }
    k := k - 1;
  }
  
  /* code modified by LLM (iteration 1): Prove that no common substring exists beyond maxLen by showing |str2| constraint */
  forall j | maxLen < j <= |str1|
    ensures !haveCommonKSubstringPredicate(j, str1, str2)
  {
    /* code modified by LLM (iteration 1): Use the fact that j > maxLen >= |str2|, so haveCommonKSubstringPredicate requires |str2| >= j which is false */
    assert j > maxLen;
    assert maxLen >= |str2|;
    assert j > |str2|;
    assert |str2| < j;
    assert !haveCommonKSubstringPredicate(j, str1, str2);
  }
}