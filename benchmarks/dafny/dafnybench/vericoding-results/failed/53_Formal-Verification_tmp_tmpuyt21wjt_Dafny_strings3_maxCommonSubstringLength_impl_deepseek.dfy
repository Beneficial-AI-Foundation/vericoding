predicate isSubstring(sub: seq<char>, str: seq<char>)
{
    exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
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
  assume{:axiom} false;
}

// <vc-helpers>
lemma HaveCommonKSubstringPredImpliesNotHaveNotCommonKSubstringPred(k: nat, str1: string, str2: string)
  requires haveCommonKSubstringPred(k, str1, str2)
  ensures !haveNotCommonKSubstringPred(k, str1, str2)
{
}

lemma NotHaveCommonKSubstringPredImpliesHaveNotCommonKSubstringPred(k: nat, str1: string, str2: string)
  requires !haveCommonKSubstringPred(k, str1, str2)
  ensures haveNotCommonKSubstringPred(k, str1, str2)
{
}

lemma ZeroLengthIsAlwaysCommon(str1: string, str2: string)
  ensures haveCommonKSubstringPred(0, str1, str2)
{
}

lemma HaveCommonKSubstringPredMonotonic(k1: nat, k2: nat, str1: string, str2: string)
  requires k1 <= k2
  requires haveCommonKSubstringPred(k2, str1, str2)
  ensures haveCommonKSubstringPred(k1, str1, str2)
{
}

lemma NotHaveCommonKSubstringPredMonotonic(k1: nat, k2: nat, str1: string, str2: string)
  requires k1 <= k2
  requires !haveCommonKSubstringPred(k1, str1, str2)
  ensures !haveCommonKSubstringPred(k2, str1, str2)
{
}

lemma HaveCommonKSubstringPredAntitone(k1: nat, k2: nat, str1: string, str2: string)
  requires k1 <= k2
  requires haveCommonKSubstringPred(k2, str1, str2)
  ensures haveCommonKSubstringPred(k1, str1, str2)
{
}

lemma NotHaveCommonKSubstringPredAntitone(k1: nat, k2: nat, str1: string, str2: string)
  requires k1 <= k2
  requires !haveCommonKSubstringPred(k1, str1, str2)
  ensures !haveCommonKSubstringPred(k2, str1, str2)
{
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
    var low := 0;
    var high := |str1|;
    len := 0;
    
    while low <= high
        invariant 0 <= low <= high + 1 <= |str1| + 1
        invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
        invariant len == 0 || haveCommonKSubstringPred(len, str1, str2)
    {
        var mid := (low + high) / 2;
        var found := haveCommonKSubstring(mid, str1, str2);
        
        if found {
            len := mid;
            low := mid + 1;
            if mid > 0 {
                assert haveCommonKSubstringPred(mid, str1, str2);
            }
            if mid < |str1| {
                NotHaveCommonKSubstringPredAntitone(mid + 1, high, str1, str2);
            }
        } else {
            high := mid - 1;
            if mid > 0 {
                assert !haveCommonKSubstringPred(mid, str1, str2);
            }
            if len < mid && mid <= |str1| {
                NotHaveCommonKSubstringPredAntitone(mid, |str1|, str1, str2);
            }
        }
    }
    
    if len == 0 {
        ZeroLengthIsAlwaysCommon(str1, str2);
    }
}
// </vc-code>

