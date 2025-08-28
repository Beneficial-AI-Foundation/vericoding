method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
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

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
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
lemma PrefixImpliesSubstring(pre: string, str: string)
  ensures isPrefixPred(pre, str) ==> isSubstringPred(pre, str)
{
  if isPrefixPred(pre, str) {
    assert isPrefixPred(pre, str[0..]);
  }
}

lemma NotPrefixImpliesNotSubstring(sub: string, str: string)
  ensures isNotPrefixPred(sub, str) ==> isNotSubstringPred(sub, str)
{
  if isNotPrefixPred(sub, str) {
    assert forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..]);
  }
}

lemma SubstringNotFoundImpliesNotCommon(k: nat, str1: string, str2: string, i: nat)
  requires 0 <= i <= |str1| - k
  requires forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
  ensures forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
{
}

lemma MaintainNotFoundInvariant(k: nat, str1: string, str2: string, i: nat, i_prev: nat)
  requires 0 <= i_prev < i <= |str1| - k + 1
  requires forall i1 :: 0 <= i1 < i_prev ==> isNotSubstringPred(str1[i1..i1+k], str2)
  requires isNotSubstringPred(str1[i_prev..i_prev+k], str2)
  ensures forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
method haveCommonKSubstringImpl(k: nat, str1: string, str2: string) returns (found: bool)
  ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
  if k == 0 || k > |str1| {
    found := false;
    return;
  }

  found := false;
  var i := 0;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant found ==> exists i1 :: 0 <= i1 < i && isSubstringPred(str1[i1..i1+k], str2)
    invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
    decreases |str1| - k - i
  {
    var substr := str1[i..i+k];
    var res := isSubstring(substr, str2);
    if res {
      found := true;
      return;
    }
    if !found {
      MaintainNotFoundInvariant(k, str1, str2, i + 1, i);
    }
    i := i + 1;
  }
}
// </vc-code>
