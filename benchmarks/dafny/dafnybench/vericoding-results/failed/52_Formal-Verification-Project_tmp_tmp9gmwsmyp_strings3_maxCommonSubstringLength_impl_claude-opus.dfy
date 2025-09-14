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
lemma haveCommonKSubstringMonotonic(k: nat, str1: string, str2: string)
    requires k > 0
    requires haveCommonKSubstringPred(k, str1, str2)
    ensures haveCommonKSubstringPred(k-1, str1, str2)
{
    // If we have a common substring of length k, we also have one of length k-1
    assert haveCommonKSubstringPred(k, str1, str2);
    var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
    
    // The prefix of length k-1 of this substring is also a common substring
    assert 0 <= i1 <= |str1| - (k-1);
    var j1' := i1 + (k-1);
    assert str1[i1..j1'][..] == str1[i1..j1'][..];
    
    // We need to show that str1[i1..j1'] is a substring of str2
    assert isSubstringPred(str1[i1..j1], str2);
    var idx :| 0 <= idx <= |str2| && isPrefixPred(str1[i1..j1], str2[idx..]);
    assert |str1[i1..j1]| == k;
    assert |str1[i1..j1']| == k-1;
    assert str1[i1..j1'][..] == str1[i1..j1][..k-1];
    assert isPrefixPred(str1[i1..j1'], str2[idx..]);
    assert isSubstringPred(str1[i1..j1'], str2);
    assert haveCommonKSubstringPred(k-1, str1, str2);
}

lemma emptyStringIsAlwaysCommon(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    if |str1| >= 0 {
        assert str1[0..0] == "";
        assert isPrefixPred("", str2[0..]);
        assert isSubstringPred("", str2);
        assert haveCommonKSubstringPred(0, str1, str2);
    }
}

method isSubstringMethod(sub: seq<char>, str: seq<char>) returns (result: bool)
    ensures result <==> isSubstringPred(sub, str)
{
    if |sub| > |str| {
        return false;
    }
    
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
        decreases |str| - |sub| - i + 1
    {
        if |sub| <= |str[i..]| && sub == str[i..][..|sub|] {
            assert isPrefixPred(sub, str[i..]);
            assert isSubstringPred(sub, str);
            return true;
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..]);
    
    // For positions after |str| - |sub|, the remaining string is too short
    forall j | |str| - |sub| < j <= |str|
        ensures !isPrefixPred(sub, str[j..])
    {
        assert |str[j..]| < |sub|;
        assert !isPrefixPred(sub, str[j..]);
    }
    
    assert forall j :: 0 <= j <= |str| ==> !isPrefixPred(sub, str[j..]);
    assert !isSubstringPred(sub, str);
    return false;
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
    var k := |str1|;
    
    // Start from the maximum possible length and work downward
    while k > 0
        invariant 0 <= k <= |str1|
        invariant forall m :: k < m <= |str1| ==> !haveCommonKSubstringPred(m, str1, str2)
        decreases k
    {
        var found := haveCommonKSubstring(k, str1, str2);
        if found {
            return k;
        }
        k := k - 1;
    }
    
    // If we reach here, k == 0
    // Empty string is always a common substring
    emptyStringIsAlwaysCommon(str1, str2);
    return 0;
}
// </vc-code>

