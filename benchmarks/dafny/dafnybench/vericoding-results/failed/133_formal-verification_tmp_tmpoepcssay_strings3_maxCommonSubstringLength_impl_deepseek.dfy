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
lemma haveCommonKSubstringPredImpliesExistsSubstring(k: nat, str1: string, str2: string)
    requires haveCommonKSubstringPred(k, str1, str2)
    ensures exists i1 :: 0 <= i1 <= |str1| - k && exists i2 :: 0 <= i2 <= |str2| - k && 
            str1[i1..i1+k] == str2[i2..i2+k]
{
    // Extract witness from the predicate
    var i1, j1 :| 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
    // Extract witness from isSubstringPred
    var i2 :| 0 <= i2 <= |str2| && isPrefixPred(str1[i1..j1], str2[i2..]);
    assert str1[i1..j1] == str2[i2..i2+k];
}

lemma haveNotCommonKSubstringPredImpliesAllSubstrings(k: nat, str1: string, str2: string)
    requires haveNotCommonKSubstringPred(k, str1, str2)
    ensures forall i1 :: 0 <= i1 <= |str1| - k ==> 
            forall i2 :: 0 <= i2 <= |str2| - k ==> str1[i1..i1+k] != str2[i2..i2+k]
{
}

lemma haveCommonKSubstringPredMonotonic(k: nat, str1: string, str2: string)
    requires k > 0 && haveCommonKSubstringPred(k, str1, str2)
    ensures haveCommonKSubstringPred(k-1, str1, str2)
{
    var i :| 0 <= i <= |str1| - k && isSubstringPred(str1[i..i+k], str2);
    // Any substring of length k-1 within the k-length substring will work
    assert isSubstringPred(str1[i..i+k-1], str2);
}

// Helper lemma to establish that if we have a common substring of length current_len,
// then we have a common substring of length len where len <= current_len
lemma commonSubstringLengthPreserved(len: nat, current_len: nat, str1: string, str2: string)
    requires len <= current_len
    requires haveCommonKSubstringPred(current_len, str1, str2)
    ensures haveCommonKSubstringPred(len, str1, str2)
{
    if len < current_len {
        haveCommonKSubstringPredMonotonic(current_len, str1, str2);
        commonSubstringLengthPreserved(len, current_len-1, str1, str2);
    }
}

// Helper lemma to show that if we found a common substring at specific positions,
// then the predicate holds
lemma foundCommonSubstringImpliesPredicate(i: nat, j: nat, k: nat, str1: string, str2: string)
    requires 0 <= i <= |str1| - k
    requires 0 <= j <= |str2| - k
    requires str1[i..i+k] == str2[j..j+k]
    ensures haveCommonKSubstringPred(k, str1, str2)
{
    // Directly construct the witness
    assert isPrefixPred(str1[i..i+k], str2[j..]);
    assert isSubstringPred(str1[i..i+k], str2);
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma zeroLengthCommonSubstring(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    // Empty substring exists at any position
    assert forall s :: isSubstringPred("", s);
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
    len := 0;
    var i := 0;
    
    zeroLengthCommonSubstring(str1, str2);
    assert haveCommonKSubstringPred(0, str1, str2);
    
    while i <= |str1|
        invariant 0 <= i <= |str1| + 1
        invariant forall k1 :: len < k1 <= |str1| ==> !haveCommonKSubstringPred(k1, str1, str2)
        invariant haveCommonKSubstringPred(len, str1, str2)
        invariant len > 0 ==> exists i' :: 0 <= i' < i && exists j :: 0 <= j <= |str2| && 
                 str1[i'..i'+len] == str2[j..j+len]
    {
        var j := 0;
        
        while j <= |str2|
            invariant 0 <= j <= |str2| + 1
            invariant forall k1 :: len < k1 <= |str1| ==> !haveCommonKSubstringPred(k1, str1, str2)
            invariant haveCommonKSubstringPred(len, str1, str2)
            invariant len > 0 ==> exists i' :: 0 <= i' < i && exists j' :: 0 <= j' <= |str2| && 
                     str1[i'..i'+len] == str2[j'..j'+len]
        {
            if j < |str2| {
                var current_len := 0;
                var max_possible := min(|str1| - i, |str2| - j);
                
                while current_len < max_possible && str1[i + current_len] == str2[j + current_len]
                    invariant 0 <= current_len <= max_possible
                    invariant forall k2 :: 0 <= k2 < current_len ==> str1[i + k2] == str2[j + k2]
                {
                    current_len := current_len + 1;
                }
                
                if current_len > len {
                    len := current_len;
                    foundCommonSubstringImpliesPredicate(i, j, len, str1, str2);
                } else if current_len > 0 {
                    foundCommonSubstringImpliesPredicate(i, j, current_len, str1, str2);
                }
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>

