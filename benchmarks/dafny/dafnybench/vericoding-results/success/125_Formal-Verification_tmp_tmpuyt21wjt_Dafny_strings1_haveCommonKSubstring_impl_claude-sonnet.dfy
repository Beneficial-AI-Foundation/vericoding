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

predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

// <vc-helpers>
lemma isPrefixEquivalence(pre: string, str: string)
  ensures isPrefixPredicate(pre, str) <==> !isNotPrefixPred(pre, str)
{
  if isPrefixPredicate(pre, str) {
    assert |str| >= |pre|;
    assert pre <= str;
    assert pre == str[..|pre|];
    assert !isNotPrefixPred(pre, str);
  }
  if !isNotPrefixPred(pre, str) {
    assert |pre| <= |str|;
    assert pre == str[..|pre|];
    assert isPrefixPredicate(pre, str);
  }
}

method isPrefixImpl(pre: string, str: string) returns (res: bool)
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
  } else {
    res := (pre == str[..|pre|]);
  }
}

method isSubstringImpl(sub: string, str: string) returns (res: bool)
  ensures res == isSubstringPredicate(sub, str)
{
  if |sub| > |str| {
    res := false;
    return;
  }
  
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
  {
    var isPrefix := isPrefixImpl(sub, str[i..]);
    if isPrefix {
      res := true;
      return;
    }
    i := i + 1;
  }
  res := false;
}
// </vc-helpers>

// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
// </vc-spec>
// <vc-code>
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
    var isSubstr := isSubstringImpl(substring, str2);
    if isSubstr {
      found := true;
      return;
    }
    i := i + 1;
  }
  found := false;
}
// </vc-code>

