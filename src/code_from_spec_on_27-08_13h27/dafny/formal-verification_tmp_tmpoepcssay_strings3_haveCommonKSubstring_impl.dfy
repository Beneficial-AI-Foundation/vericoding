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
    ensures  res ==> isSubstringPred(sub, str)
    // ensures  !res ==> !isSubstringPred(sub, str)
    ensures  isSubstringPred(sub, str) ==> res
    ensures  isSubstringPred(sub, str) ==> res
    ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
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
    requires isPrefixPred(pre, str)
    ensures isSubstringPred(pre, str)
{
    assert exists i :: i == 0 && 0 <= i <= |str| && isPrefixPred(pre, str[i..]);
}

lemma NotPrefixImpliesNotSubstringForAll(pre: string, str: string)
    requires forall i :: 0 <= i <= |str| ==> isNotPrefixPred(pre, str[i..])
    ensures isNotSubstringPred(pre, str)
{
}

lemma NoCommonSubstringImpliesNotCommonKSubstring(k: nat, str1: string, str2: string, i: nat)
    requires 0 <= i <= |str1| - k + 1
    requires forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2)
    requires i == |str1| - k + 1
    ensures haveNotCommonKSubstringPred(k, str1, str2)
{
    assert forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2);
    assert i == |str1| - k + 1;
    assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPred(str1[j..j+k], str2);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
method haveCommonKSubstringImpl(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2)
{
    if k == 0 || |str1| < k {
        found := false;
        return;
    }
    
    found := false;
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2)
        decreases |str1| - k - i
    {
        var substr := str1[i..i+k];
        var res: bool;
        res := isSubstring(substr, str2);
        if res {
            found := true;
            return;
        }
        i := i + 1;
    }
    NoCommonSubstringImpliesNotCommonKSubstring(k, str1, str2, i);
}
// </vc-code>
