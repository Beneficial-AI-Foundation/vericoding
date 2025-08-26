predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
// </vc-spec>
// <vc-code>
{
  if |pre| > |str| {
    res := false;
  } else {
    res := true;
    var i := 0;
    while i < |pre|
      invariant 0 <= i <= |pre|
      invariant res == (pre[..i] <= str)
    {
      if pre[i] != str[i] {
        res := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}




predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}