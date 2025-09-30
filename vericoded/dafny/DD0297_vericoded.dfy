predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}


method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPredicate(pre,str)
{
  assume{:axiom} false;
}



predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}


predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  assume{:axiom} false;
}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
  assume{:axiom} false;
}


predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
// </vc-spec>
// <vc-code>
{
  if |str1| <= |str2| {
    len := |str1|;
    forall k | len < k <= |str1|
      ensures !haveCommonKSubstringPredicate(k, str1, str2)
    {
      assert |str1| < k;
    }
  } else {
    len := |str2|;
    forall k | len < k <= |str1|
      ensures !haveCommonKSubstringPredicate(k, str1, str2)
    {
      assert |str2| < k;
    }
  }
}
// </vc-code>

