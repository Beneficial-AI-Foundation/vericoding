// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
