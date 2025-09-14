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
lemma SubstringTransitivity(sub: string, str1: string, str2: string, i: nat, j: nat)
  requires 0 <= i <= |str1| - |sub|
  requires isPrefixPredicate(sub, str1[i..])
  requires 0 <= j <= |str2| - |sub|
  requires isPrefixPredicate(sub, str2[j..])
  ensures sub == str1[i..i+|sub|]
  ensures sub == str2[j..j+|sub|]
{
  assert sub <= str1[i..];
  assert sub <= str2[j..];
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
    return false;
  }
  
  var i := 0;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
  {
    var candidate := (str1[i..])[..k];
    assert candidate == str1[i..i+k];
    
    var isSubstr := isSubstring(candidate, str2);
    if isSubstr {
      assert isSubstringPredicate(candidate, str2);
      assert haveCommonKSubstringPredicate(k, str1, str2);
      return true;
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPredicate((str1[j..])[..k], str2);
  assert !haveCommonKSubstringPredicate(k, str1, str2);
  return false;
}
// </vc-code>

