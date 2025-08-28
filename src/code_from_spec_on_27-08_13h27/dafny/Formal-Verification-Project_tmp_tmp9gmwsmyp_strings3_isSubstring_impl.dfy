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

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

// <vc-helpers>
lemma PrefixImpliesSubstring(sub: string, str: string)
    requires isPrefixPred(sub, str)
    ensures isSubstringPred(sub, str)
{
    assert isPrefixPred(sub, str[0..]);
}

lemma EmptyStringIsSubstring(sub: string, str: string)
    requires |sub| == 0
    ensures isSubstringPred(sub, str)
{
    assert |sub| <= |str| || |sub| == 0;
    assert isPrefixPred(sub, str[0..]);
}

lemma NotPrefixAtAllImpliesNotSubstring(sub: string, str: string)
    requires forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..])
    ensures isNotSubstringPred(sub, str)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsSubstring(sub: string, str: string) returns (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if |sub| == 0 {
        EmptyStringIsSubstring(sub, str);
        return true;
    }
    
    if |sub| > |str| {
        assert !isSubstringPred(sub, str);
        return false;
    }

    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant forall k :: 0 <= k < i ==> !isPrefixPred(sub, str[k..])
    {
        var prefixCheck := isPrefix(sub, str[i..]);
        if prefixCheck {
            assert isPrefixPred(sub, str[i..]);
            PrefixImpliesSubstring(sub, str[i..]);
            assert isSubstringPred(sub, str);
            return true;
        }
        i := i + 1;
    }
    assert forall k :: 0 <= k <= |str| - |sub| ==> !isPrefixPred(sub, str[k..]);
    NotPrefixAtAllImpliesNotSubstring(sub, str);
    assert !isSubstringPred(sub, str);
    return false;
}
// </vc-code>
