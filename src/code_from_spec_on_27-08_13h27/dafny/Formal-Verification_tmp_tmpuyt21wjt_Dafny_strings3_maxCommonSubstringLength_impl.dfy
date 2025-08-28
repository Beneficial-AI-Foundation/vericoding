predicate isSubstring(sub: seq<char>, str: seq<char>)
{
    exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

// We spent 2h each on this assignment

predicate isPrefixPred(pre:string, str:string)
{
    (|pre| <= |str|) && 
    pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}

predicate isSubstringPred(sub:string, str:string)
{
    (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
    (forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma PrefixImpliesSubstring(sub: string, str: string, i: nat)
  requires 0 <= i <= |str|
  requires isPrefixPred(sub, str[i..])
  ensures isSubstringPred(sub, str)
{
  assert str[i..i+|sub|] == sub;
}

lemma EmptyStringIsSubstring(str1: string, str2: string)
  ensures haveCommonKSubstringPred(0, str1, str2)
{
  assert |str1[0..0]| == 0;
  assert str1[0..0] == "";
  assert isPrefixPred("", str2[0..]);
  assert exists i :: 0 <= i <= |str2| && isPrefixPred("", str2[i..]);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// </vc-spec>

// <vc-code>
method MaxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires (|str1| <= |str2|)
  ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2))
  ensures haveCommonKSubstringPred(len, str1, str2)
{
  len := 0;
  var maxLen := |str1|;
  var k := maxLen;
  while k >= 0
    invariant 0 <= k <= maxLen
    invariant forall m :: k < m <= maxLen ==> !haveCommonKSubstringPred(m, str1, str2)
    invariant k < maxLen ==> forall m :: k < m <= maxLen ==> !haveCommonKSubstringPred(m, str1, str2)
  {
    var found : bool;
    found := haveCommonKSubstring(k, str1, str2);
    if found {
      len := k;
      break;
    }
    if k == 0 {
      EmptyStringIsSubstring(str1, str2);
      len := 0;
      break;
    }
    k := k - 1;
  }
}
// </vc-code>
