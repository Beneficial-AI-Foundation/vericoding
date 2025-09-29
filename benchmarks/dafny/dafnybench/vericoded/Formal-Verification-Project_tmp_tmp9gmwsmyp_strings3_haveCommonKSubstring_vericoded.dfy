method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
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

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
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
lemma haveCommonKSubstringNegation(k: nat, str1: string, str2: string)
    ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    // This follows directly from the definitions using logical negation
}
// </vc-helpers>

// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    found := false;
    if k > |str1| {
        return false;
    }
    
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant found <==> (exists i1, j1 :: 0 <= i1 < i && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2))
        invariant !found <==> (forall i1, j1 :: 0 <= i1 < i && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2))
    {
        var j := i + k;
        var sub := str1[i..j];
        var isSubstr := isSubstring(sub, str2);
        
        if isSubstr {
            found := true;
            return true;
        }
        
        i := i + 1;
    }
    
    return false;
}
// </vc-code>

