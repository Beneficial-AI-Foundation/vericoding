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
lemma NoCommonImpliesNoLonger(k: nat, str1: string, str2: string)
    requires !haveCommonKSubstringPred(k, str1, str2)
    ensures forall k' :: k' > k ==> !haveCommonKSubstringPred(k' , str1, str2)
{
    forall k' | k' > k 
        ensures !haveCommonKSubstringPred(k', str1, str2)
    {
        if haveCommonKSubstringPred(k', str1, str2) {
            var i1, j1 :| 0 <= i1 <= |str1| - k' && j1 == i1 + k' && isSubstringPred(str1[i1..j1], str2);
            assert k' > k;
            assert j1 - i1 == k';
            var sub_k := str1[i1..i1+k];
            assert sub_k == str1[i1..j1][..k];
            assert isPrefixPred(sub_k, str1[i1..j1]);
            
            var i2 :| 0 <= i2 <= |str2| && isPrefixPred(str1[i1..j1], str2[i2..]);
            assert isPrefixPred(sub_k, str2[i2..]);
            assert isSubstringPred(sub_k, str2);
            assert 0 <= i1 <= |str1| - k;
            assert haveCommonKSubstringPred(k, str1, str2);
            assert false;
        }
    }
}

lemma EmptyStringIsCommonSubstring(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    assert 0 <= 0 <= |str1| - 0;
    assert str1[0..0] == "";
    assert isPrefixPred("", str2[0..]);
    assert isSubstringPred("", str2);
    assert haveCommonKSubstringPred(0, str1, str2);
}
// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
    if |str1| == 0 {
        len := 0;
        EmptyStringIsCommonSubstring(str1, str2);
        return;
    }
    
    var k := |str1|;
    while k > 0
        invariant 0 <= k <= |str1|
        invariant forall k' :: k < k' <= |str1| ==> !haveCommonKSubstringPred(k', str1, str2)
    {
        var found := haveCommonKSubstring(k, str1, str2);
        if found {
            len := k;
            return;
        } else {
            NoCommonImpliesNoLonger(k, str1, str2);
        }
        k := k - 1;
    }
    
    len := 0;
    EmptyStringIsCommonSubstring(str1, str2);
}
// </vc-code>

