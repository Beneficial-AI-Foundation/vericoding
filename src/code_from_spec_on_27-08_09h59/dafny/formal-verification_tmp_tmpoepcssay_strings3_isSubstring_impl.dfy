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
lemma isNotSubstringEquiv(sub: string, str: string)
    ensures isNotSubstringPred(sub, str) <==> !isSubstringPred(sub, str)
{
    if isNotSubstringPred(sub, str) {
        assert forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..]);
        if isSubstringPred(sub, str) {
            var j :| 0 <= j <= |str| && isPrefixPred(sub, str[j..]);
            assert isNotPrefixPred(sub, str[j..]);
            assert false;
        }
    }
    
    if !isSubstringPred(sub, str) {
        forall i | 0 <= i <= |str|
            ensures isNotPrefixPred(sub, str[i..])
        {
            if isPrefixPred(sub, str[i..]) {
                assert isSubstringPred(sub, str);
                assert false;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    ensures  res ==> isSubstringPred(sub, str)
    // ensures  !res ==> !isSubstringPred(sub, str)
    ensures  isSubstringPred(sub, str) ==> res
    ensures  isSubstringPred(sub, str) ==> res
    ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 0;
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    {
        if i <= |str| {
            var isPref := isPrefix(sub, str[i..]);
            if isPref {
                isNotSubstringEquiv(sub, str);
                return true;
            }
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j <= |str| ==> isNotPrefixPred(sub, str[j..]);
    assert isNotSubstringPred(sub, str);
    isNotSubstringEquiv(sub, str);
    return false;
}
// </vc-code>
