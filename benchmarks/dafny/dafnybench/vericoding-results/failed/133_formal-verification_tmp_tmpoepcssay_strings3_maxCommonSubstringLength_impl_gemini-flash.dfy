predicate isSubstring(sub: string, str: string)
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
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma lemma_isPrefixPred_isNotPrefixPred(pre:string, str:string)
  ensures isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
{}

lemma lemma_isSubstringPred_isNotSubstringPred(sub:string, str:string)
  ensures isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
{
  lemma_isPrefixPred_isNotPrefixPred(sub,str[0..]); // This call is likely not strictly necessary but included for completeness.
  forall i | 0 <= i <= |str|
    ensures isPrefixPred(sub,str[i..]) <==> !isNotPrefixPred(sub,str[i..])
  {
    lemma_isPrefixPred_isNotPrefixPred(sub,str[i..]);
  }
}

lemma lemma_haveCommonKSubstringPred_haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
  ensures haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
{
  forall i1, j1 | 0 <= i1 <= |str1|- k && j1 == i1 + k
    ensures isSubstringPred(str1[i1..j1],str2) <==> !isNotSubstringPred(str1[i1..j1],str2)
  {
    lemma_isSubstringPred_isNotSubstringPred(str1[i1..j1],str2);
  }
}

// Changed from method to function to allow use in expressions.
function haveCommonKSubstring(k: nat, str1: string, str2: string) : (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2)
{
  lemma_haveCommonKSubstringPred_haveNotCommonKSubstringPred(k, str1, str2);
  haveCommonKSubstringPred(k, str1, str2)
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
    var high := |str1| + 1; // Upper bound for binary search.
    var resultLen := 0;

    // Binary search for the maximum k.
    while low < high
        invariant 0 <= low <= resultLen + 1
        invariant 0 <= resultLen <= |str1|
        invariant 0 <= high <= |str1| + 1
        invariant high > low
        invariant (forall k_inv :: high <= k_inv <= |str1| ==> !haveCommonKSubstringPred(k_inv, str1, str2))
        invariant (resultLen == 0 || haveCommonKSubstringPred(resultLen,str1,str2))
        decreases high - low
    {
        var mid := low + (high - low) / 2;

        if mid == 0 { // k=0 always exists, but we are looking for >0 common substring length.
            low := mid + 1;
            continue;
        }
        if mid > |str1| {
            high := mid;
            continue;
        }

        if haveCommonKSubstring(mid, str1, str2)  // This uses the function, which is spec'ed.
        {
            resultLen := mid;
            low := mid + 1;
        } else {
            high := mid;
        }
    }

    len := resultLen;
}
// </vc-code>

