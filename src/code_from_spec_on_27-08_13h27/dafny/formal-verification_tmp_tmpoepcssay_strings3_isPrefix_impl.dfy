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

// <vc-helpers>
lemma PrefixImpliesNotPrefix(pre: string, str: string)
  ensures isPrefixPred(pre, str) ==> !isNotPrefixPred(pre, str)
  ensures !isPrefixPred(pre, str) ==> isNotPrefixPred(pre, str)
{
  if isPrefixPred(pre, str) {
    assert |pre| <= |str| && pre == str[..|pre|];
    assert !isNotPrefixPred(pre, str);
  } else {
    assert |pre| > |str| || pre != str[..|pre|];
    assert isNotPrefixPred(pre, str);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsPrefix(pre: string, str: string) returns (res: bool)
  ensures !res <==> isNotPrefixPred(pre, str)
  ensures res <==> isPrefixPred(pre, str)
{
  if |pre| > |str| {
    res := false;
  } else {
    res := pre == str[..|pre|];
  }
  PrefixImpliesNotPrefix(pre, str);
}
// </vc-code>
