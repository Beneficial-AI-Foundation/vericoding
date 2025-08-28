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
lemma isSubstringEquivalence(sub: string, str: string)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
{
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert !isNotPrefixPred(sub, str[i..]);
        assert !isNotSubstringPred(sub, str);
    }
    
    if !isNotSubstringPred(sub, str) {
        assert exists i :: 0 <= i <= |str| && !isNotPrefixPred(sub, str[i..]);
        var i :| 0 <= i <= |str| && !isNotPrefixPred(sub, str[i..]);
        assert isPrefixPred(sub, str[i..]);
        assert isSubstringPred(sub, str);
    }
}

lemma isPrefixEquivalence(pre: string, str: string)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
{
    if isPrefixPred(pre, str) {
        assert |pre| <= |str| && pre == str[..|pre|];
        assert !isNotPrefixPred(pre, str);
    }
    
    if !isNotPrefixPred(pre, str) {
        assert !(|pre| > |str| || pre != str[..|pre|]);
        assert |pre| <= |str| && pre == str[..|pre|];
        assert isPrefixPred(pre, str);
    }
}

lemma haveCommonKSubstringEquivalence(k: nat, str1: string, str2: string)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
{
    if haveCommonKSubstringPred(k, str1, str2) {
        var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
        assert !isNotSubstringPred(str1[i1..j1], str2) by { isSubstringEquivalence(str1[i1..j1], str2); }
        assert !haveNotCommonKSubstringPred(k, str1, str2);
    }
    
    if !haveNotCommonKSubstringPred(k, str1, str2) {
        assert exists i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k && !isNotSubstringPred(str1[i1..j1], str2);
        var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && !isNotSubstringPred(str1[i1..j1], str2);
        assert isSubstringPred(str1[i1..j1], str2) by { isSubstringEquivalence(str1[i1..j1], str2); }
        assert haveCommonKSubstringPred(k, str1, str2);
    }
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
{
    found := false;
    
    if k == 0 {
        found := true;
        assert haveCommonKSubstringPred(k, str1, str2);
        return;
    }
    
    if |str1| < k {
        found := false;
        assert haveNotCommonKSubstringPred(k, str1, str2);
        assert !haveCommonKSubstringPred(k, str1, str2) by { haveCommonKSubstringEquivalence(k, str1, str2); }
        return;
    }
    
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall i1 :: {:trigger isNotSubstringPred(str1[i1..i1+k], str2)} 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
        invariant found ==> exists i1 :: 0 <= i1 < i && isSubstringPred(str1[i1..i1+k], str2)
        invariant !found ==> forall i1, j1 :: 0 <= i1 < i && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2)
        invariant found ==> exists i1, j1 :: 0 <= i1 < i && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2)
    {
        var substring := str1[i..i+k];
        var isSubRes := isSubstring(substring, str2);
        
        if isSubRes {
            found := true;
            assert isSubstringPred(str1[i..i+k], str2);
            assert 0 <= i <= |str1| - k;
            assert i + k == i + k;
            assert isSubstringPred(str1[i..i+k], str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            return;
        }
        
        assert isNotSubstringPred(str1[i..i+k], str2) by { isSubstringEquivalence(str1[i..i+k], str2); }
        i := i + 1;
    }
    
    assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2);
    assert haveNotCommonKSubstringPred(k, str1, str2);
    assert !haveCommonKSubstringPred(k, str1, str2) by { haveCommonKSubstringEquivalence(k, str1, str2); }
}
// </vc-code>
