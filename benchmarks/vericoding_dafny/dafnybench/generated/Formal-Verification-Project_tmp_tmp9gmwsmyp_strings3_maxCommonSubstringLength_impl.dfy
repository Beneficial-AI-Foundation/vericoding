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

// <vc-spec>
lemma PrefixNegationLemma(pre:string, str:string)
    ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
    ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{
    if isPrefixPred(pre,str) {
        assert |pre| <= |str| && pre == str[..|pre|];
        assert !((|pre| > |str|) || pre != str[..|pre|]);
        assert !isNotPrefixPred(pre,str);
    }
    if !isPrefixPred(pre,str) {
        assert !((|pre| <= |str|) && pre == str[..|pre|]);
        assert (|pre| > |str|) || pre != str[..|pre|];
        assert isNotPrefixPred(pre,str);
    }
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
{
    PrefixNegationLemma(sub, str);
    if isSubstringPred(sub,str) {
        var i :| 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]);
        PrefixNegationLemma(sub, str[i..]);
        assert !isNotPrefixPred(sub, str[i..]);
        assert !isNotSubstringPred(sub,str);
    }
    if !isSubstringPred(sub,str) {
        forall i | 0 <= i <= |str| 
            ensures isNotPrefixPred(sub,str[i..])
        {
            PrefixNegationLemma(sub, str[i..]);
            if isPrefixPred(sub, str[i..]) {
                assert isSubstringPred(sub,str);
                assert false;
            }
        }
        assert isNotSubstringPred(sub,str);
    }
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
{
    SubstringNegationLemma(str1, str2);
    if haveCommonKSubstringPred(k,str1,str2) {
        var i1, j1 :| 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2);
        SubstringNegationLemma(str1[i1..j1], str2);
        assert !isNotSubstringPred(str1[i1..j1],str2);
        assert !haveNotCommonKSubstringPred(k,str1,str2);
    }
    if !haveCommonKSubstringPred(k,str1,str2) {
        forall i1, j1 | 0 <= i1 <= |str1|- k && j1 == i1 + k
            ensures isNotSubstringPred(str1[i1..j1],str2)
        {
            SubstringNegationLemma(str1[i1..j1], str2);
            if isSubstringPred(str1[i1..j1],str2) {
                assert haveCommonKSubstringPred(k,str1,str2);
                assert false;
            }
        }
        assert haveNotCommonKSubstringPred(k,str1,str2);
    }
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
        // Get an index from the array position were are at to the array position that is k away and check the substring
        temp := isSubstring(str1[i..(i + k)], str2);
        if  temp == true 
        {
            IsSubstringEquivLemma(str1[i..i+k], str2);
            assert isSubstringPred(str1[i..i+k], str2);
            assert haveCommonKSubstringPred(k,str1,str2);
            return true;
        }
        assert !isSubstring(str1[i..(i + k)], str2);
        IsSubstringEquivLemma(str1[i..i+k], str2);
        assert isNotSubstringPred(str1[i..i+k], str2);
        i := i + 1;
    }
    assert forall m,n :: (0 <= m <= |str1|-k && n == m+k) ==> isNotSubstringPred(str1[m..n], str2);
    assert haveNotCommonKSubstringPred(k,str1,str2);
    commonKSubstringLemma(k,str1,str2);
    assert !haveCommonKSubstringPred(k,str1,str2);
    return false;
}

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
    assert isPrefixPred(str1[0..0], str2[0..]);
}

// <vc-helpers>
function FindSubstringIndex(sub: string, str: string): int
    requires isSubstring(sub, str)
    ensures var i := FindSubstringIndex(sub, str);
            0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
{
    FindSubstringIndexExists(sub, str);
    var i :| 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub;
    i
}

lemma FindSubstringIndexExists(sub: string, str: string)
    requires isSubstring(sub, str)
    ensures exists i {:trigger str[i..i+|sub|]} :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
{
    // The proof is trivial since isSubstring(sub, str) already contains the existential
}

lemma IsSubstringEquivLemma(sub: string, str: string)
    ensures isSubstring(sub, str) <==> isSubstringPred(sub, str)
    ensures !isSubstring(sub, str) <==> isNotSubstringPred(sub, str)
{
    if isSubstring(sub, str) {
        // Since isSubstring(sub, str) is true, we know there exists such an i
        FindSubstringIndexExists(sub, str);
        var i := FindSubstringIndex(sub, str);
        assert 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub;
        assert isPrefixPred(sub, str[i..]);
        assert isSubstringPred(sub, str);
    }
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert |sub| <= |str[i..]|;
        assert sub == str[i..][..|sub|];
        assert sub == str[i..i+|sub|];
        assert i <= |str| - |sub|;
        assert isSubstring(sub, str);
    }
    SubstringNegationLemma(sub, str);
}
// </vc-helpers>

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
    len := 0;
    haveCommon0SubstringLemma(str1, str2);
    
    var k := |str1|;
    while k > 0
        invariant 0 <= k <= |str1|
        invariant haveCommonKSubstringPred(len,str1,str2)
        invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j,str1,str2)
        invariant len <= k
        decreases k
    {
        var hasCommon := haveCommonKSubstring(k, str1, str2);
        if hasCommon {
            len := k;
            return;
        }
        k := k - 1;
    }
}
// </vc-code>