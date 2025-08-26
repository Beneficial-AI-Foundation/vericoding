predicate isSubstring(sub: seq<char>, str: seq<char>)
{
    exists i {:trigger str[i..i+|sub|]} :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

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
    ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
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
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
     if( |str1| < k || |str2| < k){
        return false;
    }
    var i := |str1| - k;
    while i >= 0
      decreases i
      invariant i >= -1 
      invariant forall j,t {:trigger isSubstringPred(str1[j..t], str2)} :: i < j <= |str1| - k && t==j+k ==> !isSubstringPred(str1[j..t], str2)
      invariant forall j {:trigger isSubstringPred(str1[j..j+k], str2)} :: i < j <= |str1| - k ==> !isSubstringPred(str1[j..j+k], str2)
    {
                var t := i+k;
        var isSub := isSubstring(str1[i..t], str2);
        if isSub 
        {
                SubstringEquivalenceLemma(str1[i..t], str2);
            return true;
        }
        assert !isSubstring(str1[i..t], str2);
        SubstringEquivalenceLemma(str1[i..t], str2);
        assert !isSubstringPred(str1[i..t], str2);
        i := i-1;
    }
    return false;
}

// <vc-helpers>
lemma SubstringEquivalenceLemma(sub: string, str: string)
    ensures isSubstring(sub, str) <==> isSubstringPred(sub, str)
{
    if isSubstring(sub, str) {
        if |sub| == 0 {
            assert sub == [];
            assert isPrefixPred([], str[0..]);
            assert isSubstringPred(sub, str);
        } else if |sub| <= |str| {
            var witness :| 0 <= witness <= |str| - |sub| && str[witness..witness+|sub|] == sub;
            assert |sub| <= |str[witness..]|;
            assert sub == str[witness..][..|sub|];
            assert isPrefixPred(sub, str[witness..]);
            assert isSubstringPred(sub, str);
        }
    }
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        assert |sub| <= |str[i..]|;
        assert sub == str[i..][..|sub|];
        if |sub| > 0 {
            assert i + |sub| <= |str|;
            assert str[i..i+|sub|] == sub;
        }
        assert isSubstring(sub, str);
    }
}

lemma EmptyStringIsCommonSubstring(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    if |str1| >= 0 {
        assert str1[0..0] == [];
        assert isPrefixPred([], str2[0..]);
        assert isSubstringPred([], str2);
        assert haveCommonKSubstringPred(0, str1, str2);
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
    len := 0;
    var k := |str1|;
    
    while k >= 1
        decreases k
        invariant 0 <= k <= |str1|
        invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2)
    {
        var hasCommon := haveCommonKSubstring(k, str1, str2);
        if hasCommon {
            len := k;
            return;
        }
        k := k - 1;
    }
    
    // k == 0 case - empty string is always a common substring
    len := 0;
    EmptyStringIsCommonSubstring(str1, str2);
}
// </vc-code>