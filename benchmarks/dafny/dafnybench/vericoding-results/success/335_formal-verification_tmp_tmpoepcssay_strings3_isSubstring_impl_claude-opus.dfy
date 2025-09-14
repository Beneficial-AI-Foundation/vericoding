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
lemma isSubstringLemma(sub: string, str: string)
    ensures isSubstringPred(sub, str) <==> exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..])
    ensures isNotSubstringPred(sub, str) <==> forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..])
{
    // These follow directly from the definitions
}
// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    ensures  res ==> isSubstringPred(sub, str)
    // ensures  !res ==> !isSubstringPred(sub, str)
    ensures  isSubstringPred(sub, str) ==> res
    ensures  isSubstringPred(sub, str) ==> res
    ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if |sub| > |str| {
        return false;
    }
    
    var i := 0;
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    {
        if i == |str| {
            if |sub| == 0 {
                assert isPrefixPred(sub, str[i..]);
                return true;
            }
            i := i + 1;
        } else {
            var prefixResult := isPrefix(sub, str[i..]);
            if prefixResult {
                assert isPrefixPred(sub, str[i..]);
                return true;
            }
            assert isNotPrefixPred(sub, str[i..]);
            i := i + 1;
        }
    }
    
    assert i == |str| + 1;
    assert forall j :: 0 <= j <= |str| ==> isNotPrefixPred(sub, str[j..]);
    return false;
}
// </vc-code>

