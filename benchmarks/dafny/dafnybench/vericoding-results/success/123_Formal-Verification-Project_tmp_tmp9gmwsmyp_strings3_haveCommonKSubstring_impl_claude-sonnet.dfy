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
lemma isSubstringCorrectness(sub: string, str: string)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
{
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert !isNotPrefixPred(sub, str[i..]);
        assert !isNotSubstringPred(sub, str);
    } else {
        assert forall i :: 0 <= i <= |str| ==> !isPrefixPred(sub, str[i..]);
        assert forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..]);
        assert isNotSubstringPred(sub, str);
    }
}

lemma isPrefixCorrectness(pre: string, str: string)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
{
    if isPrefixPred(pre, str) {
        assert |pre| <= |str| && pre == str[..|pre|];
        assert !isNotPrefixPred(pre, str);
    } else {
        assert |pre| > |str| || pre != str[..|pre|];
        assert isNotPrefixPred(pre, str);
    }
}

lemma emptyStringIsSubstring(str: string)
    ensures isSubstringPred("", str)
{
    assert isPrefixPred("", str[0..]);
    assert isSubstringPred("", str);
}

lemma haveCommonKSubstringWhenKIsZero(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    emptyStringIsSubstring(str2);
    assert isSubstringPred("", str2);
    assert str1[0..0] == "";
    assert isSubstringPred(str1[0..0], str2);
    assert haveCommonKSubstringPred(0, str1, str2);
}
// </vc-helpers>

// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        found := true;
        haveCommonKSubstringWhenKIsZero(str1, str2);
        return;
    }
    
    if |str1| < k {
        found := false;
        return;
    }
    
    found := false;
    var i := 0;
    
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall i1, j1 :: 0 <= i1 < i && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2)
        invariant found ==> haveCommonKSubstringPred(k, str1, str2)
    {
        var substring := str1[i..i+k];
        var isSubResult := isSubstring(substring, str2);
        
        if isSubResult {
            found := true;
            assert isPrefixPred(substring, str2[0..]) || (exists idx :: 0 < idx <= |str2| && isPrefixPred(substring, str2[idx..]));
            assert isSubstringPred(substring, str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            return;
        } else {
            isSubstringCorrectness(substring, str2);
            assert isNotSubstringPred(substring, str2);
        }
        
        i := i + 1;
    }
    
    assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2);
    assert haveNotCommonKSubstringPred(k, str1, str2);
    assert !haveCommonKSubstringPred(k, str1, str2);
}
// </vc-code>

