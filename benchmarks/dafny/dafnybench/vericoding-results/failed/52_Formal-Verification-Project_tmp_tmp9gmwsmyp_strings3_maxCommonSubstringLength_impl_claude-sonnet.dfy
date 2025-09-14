predicate isSubstring(sub: seq<char>, str: seq<char>)
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
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    // Check that both strings are larger than k 
    if (k > |str1| || k > |str2| ){
        return false;
    }
    // Initialize variables
    var i := 0;
    var temp := false;

    // Don't want to exceed the bounds of str1 when checking for the element that is k entries away
    while i <= |str1|-k
    // Invariant to stay within bounds
    invariant 0 <= i <= (|str1|-k) + 1
    // Invariant to show that when temp is true, it is a substring
    invariant temp ==> 0 <= i <= (|str1| - k) && isSubstringPred(str1[i..i+k], str2)
    // Invariant to show that when temp is false, it is not a substring
    invariant !temp ==> (forall m,n :: (0 <= m < i && n == m+k) ==> isNotSubstringPred(str1[m..n], str2))
    // Telling dafny that i is that value that is increasing
    decreases |str1| - k - i
    {
        assume false;

        // Get an index from the array position were are at to the array position that is k away and check the substring
        temp := isSubstring(str1[i..(i + k)], str2);
        if  temp == true 
        {
            return true;
        }
        i := i + 1;
    }
    return false;
}

// <vc-helpers>
lemma isSubstringEquivalence(sub: string, str: string)
    requires |sub| <= |str|
    ensures isSubstring(sub, str) <==> isSubstringPred(sub, str)
{
    if isSubstring(sub, str) {
        var i :| 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub;
        assert isPrefixPred(sub, str[i..]);
        assert isSubstringPred(sub, str);
    }
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert |sub| <= |str[i..]|;
        assert sub == str[i..][..|sub|];
        assert sub == str[i..i+|sub|];
        assert isSubstring(sub, str);
    }
}

lemma haveCommonKSubstringEquivalence(k: nat, str1: string, str2: string)
    requires k <= |str1|
    ensures haveCommonKSubstringPred(k, str1, str2) <==> 
            (exists i :: 0 <= i <= |str1| - k && isSubstring(str1[i..i+k], str2))
{
    if haveCommonKSubstringPred(k, str1, str2) {
        var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
        if k <= |str2| {
            isSubstringEquivalence(str1[i1..j1], str2);
        }
        assert isSubstring(str1[i1..i1+k], str2);
    }
    if exists i :: 0 <= i <= |str1| - k && isSubstring(str1[i..i+k], str2) {
        var i :| 0 <= i <= |str1| - k && isSubstring(str1[i..i+k], str2);
        if k <= |str2| {
            isSubstringEquivalence(str1[i..i+k], str2);
        }
        assert isSubstringPred(str1[i..i+k], str2);
        assert haveCommonKSubstringPred(k, str1, str2);
    }
}

lemma emptyStringIsSubstring(str: string)
    ensures isSubstring([], str)
    ensures isSubstringPred([], str)
{
    assert 0 <= 0 <= |str| - 0;
    assert str[0..0] == [];
    assert isSubstring([], str);
    assert 0 <= 0 <= |str|;
    var emptySeq: seq<char> := [];
    assert |emptySeq| <= |str[0..]|;
    assert emptySeq == str[0..][..0];
    assert isPrefixPred(emptySeq, str[0..]);
    assert isSubstringPred(emptySeq, str);
}

lemma haveCommonZeroSubstring(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    emptyStringIsSubstring(str2);
    if |str1| >= 0 {
        assert str1[0..0] == [];
        assert isSubstringPred(str1[0..0], str2);
        assert haveCommonKSubstringPred(0, str1, str2);
    }
}

lemma findSubstringWitness(sub: string, str: string)
    requires isSubstring(sub, str)
    ensures exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
{
    // The witness exists by definition of isSubstring
}

lemma findSubstringPredWitness(sub: string, str: string)
    requires isSubstringPred(sub, str)
    ensures exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..])
{
    // The witness exists by definition of isSubstringPred
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
        haveCommonZeroSubstring(str1, str2);
        return 0;
    }
    
    var k := |str1|;
    
    while k > 0
        invariant 0 <= k <= |str1|
        invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2)
        decreases k
    {
        if k <= |str2| {
            haveCommonKSubstringEquivalence(k, str1, str2);
        }
        var hasCommon := haveCommonKSubstring(k, str1, str2);
        if hasCommon {
            return k;
        }
        k := k - 1;
    }
    
    haveCommonZeroSubstring(str1, str2);
    return 0;
}
// </vc-code>

