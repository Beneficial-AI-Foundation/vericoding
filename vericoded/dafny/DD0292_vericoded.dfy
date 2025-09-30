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
lemma isNotSubstringLemma(sub: string, str: string)
    ensures isNotSubstringPred(sub, str) <==> !isSubstringPred(sub, str)
{
    if isSubstringPred(sub, str) {
        // If isSubstringPred is true, then there exists an i such that isPrefixPred(sub, str[i..])
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        // This means isNotPrefixPred(sub, str[i..]) is false
        assert !isNotPrefixPred(sub, str[i..]);
        // Therefore, isNotSubstringPred is false
        assert !isNotSubstringPred(sub, str);
    } else {
        // If isSubstringPred is false, then for all i, !isPrefixPred(sub, str[i..])
        forall i | 0 <= i <= |str|
            ensures isNotPrefixPred(sub, str[i..])
        {
            assert !isPrefixPred(sub, str[i..]);
        }
        // Therefore, isNotSubstringPred is true
        assert isNotSubstringPred(sub, str);
    }
}
// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    var i := 0;
    res := false;
    
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant res ==> (exists j :: 0 <= j < i && isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
    {
        if i > |str| {
            break;
        }
        
        var prefixRes := isPrefix(sub, str[i..]);
        if prefixRes {
            res := true;
            assert isPrefixPred(sub, str[i..]);
            assert 0 <= i < i + 1;
            i := i + 1;
            break;
        }
        
        i := i + 1;
    }
    
    if res {
        // res is true, so there exists j < i such that isPrefixPred(sub, str[j..])
        assert exists j :: 0 <= j < i && isPrefixPred(sub, str[j..]);
        var j :| 0 <= j < i && isPrefixPred(sub, str[j..]);
        assert 0 <= j <= |str|;
        assert isPrefixPred(sub, str[j..]);
        assert isSubstringPred(sub, str);
    } else {
        // res is false, so for all j < i, isNotPrefixPred(sub, str[j..])
        assert forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]);
        assert i > |str|;
        
        // Since i > |str|, we checked all positions from 0 to |str|
        forall j | 0 <= j <= |str|
            ensures isNotPrefixPred(sub, str[j..])
        {
            assert j < i;
            assert isNotPrefixPred(sub, str[j..]);
        }
        
        assert isNotSubstringPred(sub, str);
        isNotSubstringLemma(sub, str);
        assert !isSubstringPred(sub, str);
    }
}
// </vc-code>

