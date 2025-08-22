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

//IMPL maxCommonSubstringLength

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  /* code modified by LLM (iteration 1): Added helper lemma for values beyond |str2| */
  lemma NoCommonSubstringBeyondStr2(s1: string, s2: string, k: nat)
    requires k > |s2|
    ensures !haveCommonKSubstringPredicate(k, s1, s2)
  {
    // If k > |s2|, then |s2| < k, so haveCommonKSubstringPredicate is false
  }
  
  /* code modified by LLM (iteration 1): Fixed bounds and added proper invariants */
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  len := 0;
  
  var k := maxLen;
  /* code modified by LLM (iteration 1): Updated loop with complete invariants */
  while k > 0
    invariant 0 <= k <= maxLen
    invariant maxLen <= |str1| && maxLen <= |str2|
    invariant len <= |str1| && len <= |str2|
    invariant forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
    decreases k
  {
    var found := haveCommonKSubstring(k, str1, str2);
    if found {
      len := k;
      /* code modified by LLM (iteration 1): Establish postcondition using helper lemma */
      forall j | len < j <= |str1|
        ensures !haveCommonKSubstringPredicate(j, str1, str2)
      {
        if j <= maxLen {
          // Follows from loop invariant
        } else {
          // j > maxLen >= |str2|, so use helper lemma
          NoCommonSubstringBeyondStr2(str1, str2, j);
        }
      }
      return;
    }
    k := k - 1;
  }
  
  /* code modified by LLM (iteration 1): Handle case when no common substring found */
  forall j | 0 < j <= |str1|
    ensures !haveCommonKSubstringPredicate(j, str1, str2)
  {
    if j <= maxLen {
      // Follows from loop invariant (k = 0, so 0 < j <= maxLen)
    } else {
      // j > maxLen >= |str2|, so use helper lemma
      NoCommonSubstringBeyondStr2(str1, str2, j);
    }
  }
  len := 0;
}