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
lemma haveCommonKSubstringMonotonicity(k1: nat, k2: nat, str1: string, str2: string)
  requires k1 <= k2
  requires haveCommonKSubstringPredicate(k2, str1, str2)
  ensures haveCommonKSubstringPredicate(k1, str1, str2)
{
  if |str1| < k1 || |str2| < k1 {
    return;
  }
  
  if k1 == 0 {
    assert haveCommonKSubstringPredicate(0, str1, str2);
    return;
  }
  
  assert |str1| >= k2 && |str2| >= k2;
  var i :| 0 <= i <= |str1| - k2 && isSubstringPredicate((str1[i..])[..k2], str2);
  
  assert 0 <= i <= |str1| - k1;
  assert (str1[i..])[..k1] == (str1[i..])[..k2][..k1];
  
  assert isSubstringPredicate((str1[i..])[..k1], str2);
  assert haveCommonKSubstringPredicate(k1, str1, str2);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
// </vc-spec>
// </vc-spec>

// <vc-code>
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
      
      forall j | len < j <= |str1|
        ensures !haveCommonKSubstringPredicate(j, str1, str2)
      {
        if j <= maxLen {
          assert !haveCommonKSubstringPredicate(j, str1, str2);
        } else {
          assert j > |str2|;
          assert !haveCommonKSubstringPredicate(j, str1, str2);
        }
      }
      
      return;
    }
    k := k - 1;
  }
  
  len := 0;
  
  forall j | 0 < j <= |str1|
    ensures !haveCommonKSubstringPredicate(j, str1, str2)
  {
    if j <= maxLen {
      assert !haveCommonKSubstringPredicate(j, str1, str2);
    } else {
      assert j > |str2|;
      assert !haveCommonKSubstringPredicate(j, str1, str2);
    }
  }
}
// </vc-code>
