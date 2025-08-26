predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}


// <vc-spec>
method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPredicate(pre,str)
{
    if |str| < |pre| 
    {
        return false;
    }
    else if pre[..] == str[..|pre|]
    {
        return true;
    }
    else{
        return false;
    }
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
    if |sub| > |str| {
        return false;
    }

    var i := |str| - |sub|;
    while i >= 0 
    decreases i
    invariant i >= -1
    invariant forall j :: i <  j <= |str|-|sub| ==> !(isPrefixPredicate(sub, str[j..]))
    {
        var isPref := isPrefix(sub, str[i..]);
        if isPref
        {
            return true;
        }
        i := i-1;
    }
    return false;
}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}

// <vc-helpers>
// </vc-helpers>

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
// </vc-spec>
// <vc-code>
{
  if |str1| < k || |str2| < k {
    return false;
  }
  
  var i := 0;
  while i <= |str1| - k
    decreases |str1| - k - i
    invariant 0 <= i <= |str1| - k + 1
    invariant forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
  {
    var substring := (str1[i..])[..k];
    var isSubstr := isSubstring(substring, str2);
    if isSubstr {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}