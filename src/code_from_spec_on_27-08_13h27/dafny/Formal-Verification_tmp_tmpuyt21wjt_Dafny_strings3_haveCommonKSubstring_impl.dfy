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
method isPrefixImpl(pre: string, str: string) returns (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if |pre| > |str| {
        return false;
    }
    var i := 0;
    while i < |pre|
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    {
        if pre[i] != str[i] {
            return false;
        }
        i := i + 1;
    }
    return true;
}

method isSubstringImpl(sub: string, str: string) returns (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if |sub| > |str| {
        return false;
    }
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    {
        var prefixRes := isPrefixImpl(sub, str[i..]);
        if prefixRes {
            return true;
        }
        i := i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
method haveCommonKSubstringImpl(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k == 0 || k > |str1| {
        return false;
    }
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2)
    {
        var sub := str1[i..i+k];
        var res := isSubstringImpl(sub, str2);
        if res {
            return true;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>
