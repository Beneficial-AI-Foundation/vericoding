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
lemma CommonSubstringMonotonicity(k: nat, str1: string, str2: string)
    requires k > 0
    requires haveCommonKSubstringPred(k, str1, str2)
    ensures haveCommonKSubstringPred(k-1, str1, str2)
{
    // If there's a common substring of length k, there's also one of length k-1
    assert haveCommonKSubstringPred(k, str1, str2);
    var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
    
    // Take the first k-1 characters of the same substring
    var i1' := i1;
    var j1' := i1 + (k-1);
    assert 0 <= i1' <= |str1| - (k-1);
    assert j1' == i1' + (k-1);
    
    // Show that str1[i1'..j1'] is a substring of str2
    var i2 :| 0 <= i2 <= |str2| && isPrefixPred(str1[i1..j1], str2[i2..]);
    assert isPrefixPred(str1[i1'..j1'], str2[i2..]);
    assert isSubstringPred(str1[i1'..j1'], str2);
    assert haveCommonKSubstringPred(k-1, str1, str2);
}

lemma NoCommonSubstringMonotonicity(k: nat, str1: string, str2: string)
    requires !haveCommonKSubstringPred(k, str1, str2)
    ensures forall j :: j >= k ==> !haveCommonKSubstringPred(j, str1, str2)
{
    forall j | j >= k
        ensures !haveCommonKSubstringPred(j, str1, str2)
    {
        if j > |str1| {
            // Can't have a substring longer than str1
            assert !haveCommonKSubstringPred(j, str1, str2);
        } else if haveCommonKSubstringPred(j, str1, str2) {
            // If we have a common substring of length j >= k, we also have one of length k
            var steps := j - k;
            var curr := j;
            while curr > k
                invariant k <= curr <= j
                invariant haveCommonKSubstringPred(curr, str1, str2)
            {
                CommonSubstringMonotonicity(curr, str1, str2);
                curr := curr - 1;
            }
            assert haveCommonKSubstringPred(k, str1, str2);
            assert false;  // Contradiction
        }
    }
}

lemma EmptySubstringAlwaysExists(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    // The empty string is always a substring
    assert 0 <= 0 <= |str1| - 0;
    var i1 := 0;
    var j1 := 0;
    assert str1[i1..j1] == "";
    assert isPrefixPred("", str2[0..]);
    assert isSubstringPred("", str2);
    assert haveCommonKSubstringPred(0, str1, str2);
}

lemma NoCommonSubstringAboveLength(str1: string, str2: string)
    ensures forall k :: |str1| < k ==> !haveCommonKSubstringPred(k, str1, str2)
{
    forall k | |str1| < k
        ensures !haveCommonKSubstringPred(k, str1, str2)
    {
        if haveCommonKSubstringPred(k, str1, str2) {
            var i1, j1 :| 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
            assert i1 <= |str1| - k;
            assert k > |str1|;
            assert i1 <= |str1| - k < 0;
            assert false;
        }
    }
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
    // Binary search for the maximum length
    var low := 0;
    var high := |str1|;
    
    EmptySubstringAlwaysExists(str1, str2);
    NoCommonSubstringAboveLength(str1, str2);
    
    // Invariant: there's a common substring of length low, but not of length high+1
    while low < high
        invariant 0 <= low <= high <= |str1|
        invariant haveCommonKSubstringPred(low, str1, str2)
        invariant forall k :: high < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    {
        var mid := (low + high + 1) / 2;
        var found := haveCommonKSubstring(mid, str1, str2);
        
        if found {
            low := mid;
        } else {
            // mid doesn't have a common substring, so neither does anything larger
            NoCommonSubstringMonotonicity(mid, str1, str2);
            high := mid - 1;
        }
    }
    
    len := low;
}
// </vc-code>

