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

// <vc-spec>
lemma PrefixNegationLemma(pre:string, str:string)
    ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
    ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
    if |pre| > |str|
        {return false;}

    var i := 0;
    while i < |pre|
        decreases |pre| - i
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    {
        if pre[i] != str[i]
        {
            return false;
        } 
        i := i + 1;
    }
    return true;
}
predicate isSubstringPred(sub:string, str:string)
{
    (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
    (forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
    ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
    ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    if |sub| > |str| {
        return false;
    }

    var i := |str| - |sub|;
    while i >= 0 
    decreases i
    invariant i >= -1
    invariant forall j :: i <  j <= |str|-|sub| ==> !(isPrefixPred(sub, str[j..]))
    {
        var isPref := isPrefix(sub, str[i..]);
        if isPref
        {
            return true;
        }
        i := i-1;
    }
    return false;
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
    ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
    ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

// <vc-helpers>
lemma HelperLemma(k: nat, str1: string, str2: string, i1: int)
    requires 0 <= i1 <= |str1| - k
    ensures str1[i1..i1+k] == str1[i1..i1+k]
{}

lemma MaintenanceInvariantLemma(k: nat, str1: string, str2: string, i1: int)
    requires 0 <= i1 <= |str1| - k
    requires !isSubstringPred(str1[i1..i1+k], str2)
    requires forall i :: 0 <= i < i1 ==> !isSubstringPred(str1[i..i+k], str2)
    ensures forall i :: 0 <= i < i1 + 1 ==> !isSubstringPred(str1[i..i+k], str2)
{}

lemma FinalAssertionLemma(k: nat, str1: string, str2: string, bound: int)
    requires k <= |str1|
    requires bound == |str1| - k + 1
    requires forall i :: 0 <= i < bound ==> !isSubstringPred(str1[i..i+k], str2)
    ensures forall i :: 0 <= i <= |str1| - k ==> !isSubstringPred(str1[i..i+k], str2)
{
    forall i | 0 <= i <= |str1| - k 
        ensures !isSubstringPred(str1[i..i+k], str2)
    {
        assert 0 <= i < bound;
    }
}

lemma HaveNotCommonLemma(k: nat, str1: string, str2: string)
    requires k <= |str1|
    requires forall i :: 0 <= i <= |str1| - k ==> !isSubstringPred(str1[i..i+k], str2)
    ensures haveNotCommonKSubstringPred(k, str1, str2)
{
    forall i1, j1 | 0 <= i1 <= |str1| - k && j1 == i1 + k
        ensures isNotSubstringPred(str1[i1..j1], str2)
    {
        assert !isSubstringPred(str1[i1..j1], str2);
        SubstringNegationLemma(str1[i1..j1], str2);
    }
}
// </vc-helpers>

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if k > |str1| || k > |str2| {
        return false;
    }
    
    var i1 := 0;
    while i1 <= |str1| - k
        decreases |str1| - i1
        invariant 0 <= i1 <= |str1| - k + 1
        invariant forall i :: 0 <= i < i1 ==> !isSubstringPred(str1[i..i+k], str2)
    {
        var substring := str1[i1..i1+k];
        var isInStr2 := isSubstring(substring, str2);
        if isInStr2 {
            assert isSubstringPred(str1[i1..i1+k], str2);
            assert exists i :: 0 <= i <= |str1| - k && isSubstringPred(str1[i..i+k], str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            return true;
        }
        MaintenanceInvariantLemma(k, str1, str2, i1);
        i1 := i1 + 1;
    }
    
    // Prove that no common k-substring exists
    FinalAssertionLemma(k, str1, str2, |str1| - k + 1);
    assert forall i :: 0 <= i <= |str1| - k ==> !isSubstringPred(str1[i..i+k], str2);
    HaveNotCommonLemma(k, str1, str2);
    assert haveNotCommonKSubstringPred(k, str1, str2);
    commonKSubstringLemma(k, str1, str2);
    
    return false;
}
// </vc-code>