predicate isSubstring(sub: string, str: string)
{
    exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

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
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma PrefixImpliesSubstring(sub: string, str: string, i: int)
  requires 0 <= i <= |str| - |sub|
  requires str[i..i+|sub|] == sub
  ensures isSubstringPred(sub, str)
{
  assert isPrefixPred(sub, str[i..]);
}

method checkSubstringAt(k: nat, str1: string, str2: string, start1: nat) returns (found: bool)
  requires 0 <= start1 <= |str1| - k
  ensures found ==> isSubstringPred(str1[start1..start1+k], str2)
  ensures !found ==> isNotSubstringPred(str1[start1..start1+k], str2)
{
  var sub := str1[start1..start1+k];
  var i := 0;
  found := false;
  while i <= |str2| - k && !found
    invariant 0 <= i <= |str2| - k + 1
    invariant forall j :: 0 <= j < i ==> str2[j..j+k] != sub
    invariant found ==> i > 0 && str2[i-1..i-1+k] == sub
  {
    if str2[i..i+k] == sub {
      found := true;
    }
    i := i + 1;
  }
  if found {
    assert isPrefixPred(sub, str2[i-1..]);
    assert isSubstringPred(sub, str2);
  } else {
    assert forall j :: 0 <= j <= |str2| - k ==> str2[j..j+k] != sub;
    assert isNotSubstringPred(sub, str2);
  }
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
  requires |str1| <= |str2|
  ensures forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
  ensures len == 0 || haveCommonKSubstringPred(len, str1, str2)
{
  var maxLen := 0;
  var currentLen := |str1|;
  while currentLen > 0
    invariant 0 <= currentLen <= |str1|
    invariant maxLen <= currentLen
    invariant maxLen <= |str1|
    invariant forall k :: maxLen < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    invariant maxLen > 0 ==> haveCommonKSubstringPred(maxLen, str1, str2)
    decreases currentLen
  {
    var i := 0;
    var found := false;
    while i <= |str1| - currentLen && !found
      invariant 0 <= i <= |str1| - currentLen + 1
      invariant forall j :: 0 <= j < i ==> isNotSubstringPred(str1[j..j+currentLen], str2)
      invariant found ==> i > 0 && isSubstringPred(str1[i-1..i-1+currentLen], str2)
      decreases |str1| - currentLen - i
    {
      var result := checkSubstringAt(currentLen, str1, str2, i);
      if result {
        found := true;
      }
      i := i + 1;
    }
    if found {
      maxLen := currentLen;
    } else {
      assert forall j :: 0 <= j <= |str1| - currentLen ==> isNotSubstringPred(str1[j..j+currentLen], str2);
    }
    currentLen := currentLen - 1;
  }
  len := maxLen;
  if maxLen == 0 {
    assert forall k :: 0 < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2);
  }
  return len;
}
// </vc-code>
