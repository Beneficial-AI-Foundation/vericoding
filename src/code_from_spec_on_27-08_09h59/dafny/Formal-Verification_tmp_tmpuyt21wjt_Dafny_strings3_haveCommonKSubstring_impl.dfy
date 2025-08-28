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

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
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
lemma EquivalenceOfNotPredicates(pre: string, str: string)
    ensures isNotPrefixPred(pre, str) <==> !isPrefixPred(pre, str)
{
}

lemma EquivalenceOfNotSubstringPredicates(sub: string, str: string)
    ensures isNotSubstringPred(sub, str) <==> !isSubstringPred(sub, str)
{
    if isNotSubstringPred(sub, str) {
        if isSubstringPred(sub, str) {
            var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
            assert isNotPrefixPred(sub, str[i..]);
            EquivalenceOfNotPredicates(sub, str[i..]);
            assert false;
        }
    }
    
    if !isSubstringPred(sub, str) {
        forall i | 0 <= i <= |str|
            ensures isNotPrefixPred(sub, str[i..])
        {
            if !isNotPrefixPred(sub, str[i..]) {
                EquivalenceOfNotPredicates(sub, str[i..]);
                assert isPrefixPred(sub, str[i..]);
                assert isSubstringPred(sub, str);
                assert false;
            }
        }
    }
}

lemma EmptyStringIsSubstring(str: string)
    ensures isSubstringPred("", str)
{
    assert isPrefixPred("", str[0..]);
    assert isSubstringPred("", str);
}

lemma LoopMaintainsNotFound(k: nat, str1: string, str2: string, i: int)
    requires k > 0
    requires 0 <= i < |str1| - k + 1
    requires forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
    requires isNotSubstringPred(str1[i..i+k], str2)
    ensures forall i1 :: 0 <= i1 < i + 1 ==> isNotSubstringPred(str1[i1..i1+k], str2)
{
}

lemma PostconditionProof(k: nat, str1: string, str2: string, found: bool, finalI: int)
    requires k > 0
    requires |str1| >= k
    requires 0 <= finalI <= |str1| - k + 1
    requires !found ==> forall i1 :: 0 <= i1 < finalI ==> isNotSubstringPred(str1[i1..i1+k], str2)
    requires !found ==> finalI == |str1| - k + 1
    requires found ==> exists i1 :: 0 <= i1 < finalI && isSubstringPred(str1[i1..i1+k], str2)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if found {
        var i1 :| 0 <= i1 < finalI && isSubstringPred(str1[i1..i1+k], str2);
        assert 0 <= i1 <= |str1| - k;
        var j1 := i1 + k;
        assert j1 == i1 + k;
        assert str1[i1..j1] == str1[i1..i1+k];
        assert isSubstringPred(str1[i1..j1], str2);
        assert haveCommonKSubstringPred(k, str1, str2);
    } else {
        assert finalI == |str1| - k + 1;
        assert forall i1 :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2);
        if haveCommonKSubstringPred(k, str1, str2) {
            var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
            assert str1[i1..j1] == str1[i1..i1+k];
            assert isSubstringPred(str1[i1..i1+k], str2);
            assert isNotSubstringPred(str1[i1..i1+k], str2);
            EquivalenceOfNotSubstringPredicates(str1[i1..i1+k], str2);
            assert false;
        }
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
        EmptyStringIsSubstring(str2);
        found := true;
        assert haveCommonKSubstringPred(k, str1, str2);
        return;
    }
    if |str1| < k {
        found := false;
        assert !haveCommonKSubstringPred(k, str1, str2);
        return;
    }
    
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
        invariant found ==> exists i1 :: 0 <= i1 < i && isSubstringPred(str1[i1..i1+k], str2)
    {
        var substring := str1[i..i+k];
        var isSubstr := isSubstring(substring, str2);
        
        if isSubstr {
            found := true;
            assert isSubstringPred(str1[i..i+k], str2);
            PostconditionProof(k, str1, str2, found, i + 1);
            return;
        } else {
            EquivalenceOfNotSubstringPredicates(substring, str2);
            assert isNotSubstringPred(substring, str2);
            LoopMaintainsNotFound(k, str1, str2, i);
        }
        
        i := i + 1;
    }
    
    PostconditionProof(k, str1, str2, found, i);
}
// </vc-code>
