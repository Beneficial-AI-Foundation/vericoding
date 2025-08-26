- We need to prove this before incrementing `i1` to maintain the invariant
- The final assertions need to connect `i1 == |str1| - k + 1` with the range `0 <= idx <= |str1| - k`

<vc-helpers>
</vc-helpers>

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if k > |str1| {
        return false;
    }
    
    if k == 0 {
        assert isPrefixPred(str1[0..0], str2[0..]);
        assert isSubstringPred(str1[0..0], str2);
        return true;
    }
    
    var i1 := 0;
    while i1 <= |str1| - k
        invariant 0 <= i1 <= |str1| - k + 1
        invariant forall idx {:trigger str1[idx..idx+k]} :: 0 <= idx < i1 ==> !isSubstringPred(str1[idx..idx+k], str2)
        decreases |str1| - k - i1
    {
        var substring := str1[i1..i1+k];
        var isInStr2 := isSubstring(substring, str2);
        if isInStr2 {
            assert isSubstringPred(str1[i1..i1+k], str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            return true;
        }
        // We know !isInStr2, so !isSubstringPred(str1[i1..i1+k], str2)
        // This will help maintain the invariant when i1 is incremented
        assert !isSubstringPred(str1[i1..i1+k], str2);
        i1 := i1 + 1;
    }
    
    // At this point i1 == |str1| - k + 1
    assert forall idx {:trigger str1[idx..idx+k]} :: 0 <= idx < i1 ==> !isSubstringPred(str1[idx..idx+k], str2);
    assert i1 == |str1| - k + 1;
    // Since i1 == |str1| - k + 1, we have 0 <= idx < i1 <==> 0 <= idx <= |str1| - k
    assert forall idx {:trigger str1[idx..idx+k]} :: 0 <= idx <= |str1| - k ==> !isSubstringPred(str1[idx..idx+k], str2);
    assert !haveCommonKSubstringPred(k, str1, str2);
    return false;
}
// </vc-code>

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
    assert isPrefixPred(str1[0..0], str2[0..]);
}