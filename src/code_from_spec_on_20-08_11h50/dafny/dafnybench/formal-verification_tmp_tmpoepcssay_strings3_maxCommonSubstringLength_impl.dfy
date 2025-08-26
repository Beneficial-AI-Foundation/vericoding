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

// <vc-spec>
lemma PrefixNegationLemma(pre:string, str:string)
    ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
    ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

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
    ensures !isNotSubstringPred(sub,str) <==>  isSubstringPred(sub,str)
{}




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

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    if (k <= |str1| && k <= |str2|)
    {
        var slice : string;
        found := false;
        var i: nat := 0;

        while (i <= |str1| - k && found == false)
        decreases |str1| - k - i + (if !found then 1 else 0)
        invariant found ==> haveCommonKSubstringPred(k,str1,str2)
        invariant forall x, y :: 0 <= x < i && found == false && y == x + k && y <= |str1| ==> isNotSubstringPred(str1[x..y], str2)     
        {
            slice := str1[i..i+k];
            found := isSubstring(slice, str2);
            if (found) {
                isSubstringToIsSubstringPredLemma(slice, str2);
                assert isSubstringPred(str1[i..i+k], str2);
                assert haveCommonKSubstringPred(k, str1, str2);
            } else {
                isSubstringToIsSubstringPredLemma(slice, str2);
                assert isNotSubstringPred(str1[i..i+k], str2);
            }
            i := i + 1;
        }
    } else {
        return false;
    }

}

// <vc-helpers>
lemma haveCommonKSubstringZeroLemma(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    // An empty substring always exists
    assert isPrefixPred("", str2[0..]);
    assert isSubstringPred("", str2);
    assert str1[0..0] == "";
}

method findSubstringIndex(sub: string, str: string) returns (idx: int)
    requires isSubstring(sub, str)
    ensures 0 <= idx <= |str| - |sub|
    ensures str[idx..idx+|sub|] == sub
{
    idx := 0;
    while idx <= |str| - |sub|
        invariant 0 <= idx <= |str| - |sub| + 1
        decreases |str| - |sub| - idx + 1
    {
        if str[idx..idx+|sub|] == sub {
            return idx;
        }
        idx := idx + 1;
    }
    // This should never be reached due to precondition
    assert false;
}

lemma isSubstringToIsSubstringPredLemma(sub: string, str: string)
    ensures isSubstring(sub, str) <==> isSubstringPred(sub, str)
{
    if isSubstring(sub, str) {
        // Find an index where substring occurs
        var i := 0;
        while i <= |str| - |sub|
            invariant 0 <= i <= |str| - |sub| + 1
            invariant exists j :: i <= j <= |str| - |sub| && str[j..j+|sub|] == sub
            decreases |str| - |sub| - i + 1
        {
            if str[i..i+|sub|] == sub {
                assert str[i..i+|sub|] == sub;
                assert isPrefixPred(sub, str[i..]);
                assert isSubstringPred(sub, str);
                return;
            }
            i := i + 1;
        }
    }
    
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert |sub| <= |str[i..]|;
        assert sub == str[i..][..|sub|];
        assert sub == str[i..i+|sub|];
        assert i + |sub| <= |str|;
        assert 0 <= i <= |str| - |sub|;
        assert isSubstring(sub, str);
    }
}
// </vc-helpers>

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
    len := |str1|;
    while (len > 0)
        decreases len
        invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2)
    {
        var hasCommon := haveCommonKSubstring(len, str1, str2);
        if (hasCommon) {
            return len;
        }
        len := len - 1;
    }
    len := 0;
    haveCommonKSubstringZeroLemma(str1, str2);
}
// </vc-code>