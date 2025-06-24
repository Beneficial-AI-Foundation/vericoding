// ATOM 
predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

//IMPL isPrefix
method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
  } else {
    res := pre <= str;
  }
}

// ATOM 
predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

//IMPL isSubstring
method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  if |str| < |sub| {
    res := false;
    return;
  }
  
  var i := 0;
  res := false;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
    invariant res ==> exists j :: 0 <= j < i && isPrefixPredicate(sub, str[j..])
  {
    var prefixRes := isPrefix(sub, str[i..]);
    if prefixRes {
      res := true;
      return;
    }
    i := i + 1;
  }
}

// ATOM 
predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
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
  
  var i := 0;
  found := false;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
    invariant found ==> exists j :: 0 <= j < i && isSubstringPredicate((str1[j..])[..k], str2)
  {
    var substring := (str1[i..])[..k];
    var substringRes := isSubstring(substring, str2);
    if substringRes {
      found := true;
      return;
    }
    i := i + 1;
  }
}

// ATOM 
predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

//IMPL maxCommonSubstringLength
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  len := 0;
  
  var k := maxLen;
  while k > 0
    invariant 0 <= k <= maxLen
    invariant forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
    invariant len <= maxLen
    decreases k
  {
    var hasCommon := haveCommonKSubstring(k, str1, str2);
    if hasCommon {
      len := k;
      return;
    }
    k := k - 1;
  }
}