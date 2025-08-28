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
lemma NotPrefixEquivalence(pre: string, str: string)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
    ensures isNotPrefixPred(pre, str) <==> !isPrefixPred(pre, str)
{
}

lemma SubstringEquivalence(sub: string, str: string)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
    ensures isNotSubstringPred(sub, str) <==> !isSubstringPred(sub, str)
{
}

lemma CommonKSubstringEquivalence(k: nat, str1: string, str2: string)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
    ensures haveNotCommonKSubstringPred(k, str1, str2) <==> !haveCommonKSubstringPred(k, str1, str2)
{
}

lemma LoopInvariantHelper(k: nat, str1: string, str2: string, i: nat)
    requires 0 <= i <= |str1| - k
    requires forall i1 {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
    ensures forall i1 {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 < i+1 && i1 != i ==> isNotSubstringPred(str1[i1..i1+k], str2)
{
}

lemma FoundImpliesCommon(k: nat, str1: string, str2: string, i: nat)
    requires 0 <= i <= |str1| - k
    requires isSubstringPred(str1[i..i+k], str2)
    ensures haveCommonKSubstringPred(k, str1, str2)
{
}

lemma NotFoundImpliesNoCommon(k: nat, str1: string, str2: string)
    requires k > 0
    requires |str1| >= k
    requires forall i1 {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2)
    ensures !haveCommonKSubstringPred(k, str1, str2)
{
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
{
    if k == 0 {
        found := true;
        return;
    }
    
    if |str1| < k {
        found := false;
        CommonKSubstringEquivalence(k, str1, str2);
        return;
    }
    
    found := false;
    var i := 0;
    
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall i1 {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
        invariant found ==> exists i1 {:trigger isSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 < i && isSubstringPred(str1[i1..i1+k], str2)
        invariant found ==> haveCommonKSubstringPred(k, str1, str2)
    {
        var substring := str1[i..i+k];
        var isSubstr := isSubstring(substring, str2);
        
        if isSubstr {
            found := true;
            FoundImpliesCommon(k, str1, str2, i);
            return;
        }
        
        i := i + 1;
    }
    
    assert forall i1 {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2);
    NotFoundImpliesNoCommon(k, str1, str2);
    CommonKSubstringEquivalence(k, str1, str2);
}
// </vc-code>
