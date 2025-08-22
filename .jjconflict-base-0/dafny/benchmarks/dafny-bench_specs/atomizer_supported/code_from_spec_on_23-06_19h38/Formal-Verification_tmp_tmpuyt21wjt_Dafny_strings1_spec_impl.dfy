// ATOM 
predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

//IMPL 
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

//IMPL 
method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  if |str| < |sub| {
    res := false;
    return;
  }
  
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
  res := false;
}

// ATOM 
predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}

//IMPL 
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
  if |str1| < k || |str2| < k {
    found := false;
    return;
  }
  
  var i := 0;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
  {
    var substring := (str1[i..])[..k];
    var substringRes := isSubstring(substring, str2);
    if substringRes {
      found := true;
      return;
    }
    i := i + 1;
  }
  found := false;
}

// ATOM 
predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

//IMPL 
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  var k := maxLen;
  
  while k > 0
    invariant 0 <= k <= maxLen
    invariant forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
    decreases k
  {
    var hasCommon := haveCommonKSubstring(k, str1, str2);
    if hasCommon {
      len := k;
      return;
    }
    k := k - 1;
  }
  len := 0;
}