predicate isSubstring(sub: seq<char>, str: seq<char>)
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
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    // Check that both strings are larger than k 
    if (k > |str1| || k > |str2| ){
        return false;
    }
    // Initialize variables
    var i := 0;
    var temp := false;

    // Don't want to exceed the bounds of str1 when checking for the element that is k entries away
    while i <= |str1|-k
    // Invariant to stay within bounds
    invariant 0 <= i <= (|str1|-k) + 1
    // Invariant to show that when temp is true, it is a substring
    invariant temp ==> 0 <= i <= (|str1| - k) && isSubstringPred(str1[i..i+k], str2)
    // Invariant to show that when temp is false, it is not a substring
    invariant !temp ==> (forall m,n :: (0 <= m < i && n == m+k) ==> isNotSubstringPred(str1[m..n], str2))
    // Telling dafny that i is that value that is increasing
    decreases |str1| - k - i
    {
        assume false;

        // Get an index from the array position were are at to the array position that is k away and check the substring
        temp := isSubstring(str1[i..(i + k)], str2);
        if  temp == true 
        {
            return true;
        }
        i := i + 1;
    }
    return false;
}

// <vc-helpers>
predicate isSubstring(sub: seq<char>, str: seq<char>)
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

lemma lemma_substring_prefix(sub: seq<char>, str: seq<char>)
    requires isSubstring(sub, str)
    ensures exists i :: 0 <= i <= |str| - |sub| && isPrefixPred(sub, str[i..])
{
    var i :| 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub;
    assert isPrefixPred(sub, str[i..]);
}

lemma lemma_prefix_substring(sub: seq<char>, str: seq<char>)
    requires exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..])
    ensures isSubstring(sub, str)
{
    var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
    assert str[i..i+|sub|] == sub;
    assert i <= |str| - |sub|;
}

lemma lemma_common_k_helper(k: nat, str1: string, str2: string)
    ensures haveCommonKSubstringPred(k,str1,str2) <==> 
        (exists i1 :: 0 <= i1 <= |str1|-k && isSubstringPred(str1[i1..i1+k],str2))
{
    calc {
        haveCommonKSubstringPred(k,str1,str2);
    ==  // def
        exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2);
    ==  // rewrite j1
        exists i1 :: 0 <= i1 <= |str1|- k && isSubstringPred(str1[i1..i1+k],str2);
    }
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
{
    if k > |str1| || k > |str2| {
        return false;
    }
    
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant forall m :: 0 <= m < i ==> !isSubstringPred(str1[m..m+k], str2)
    {
        if isSubstring(str1[i..i+k], str2) {
            lemma_prefix_substring(str1[i..i+k], str2);
            return true;
        }
        i := i + 1;
    }
    return false;
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
    var high := |str1| + 1;
    
    while high - low > 1
        invariant 0 <= low < high <= |str1| + 1
        invariant haveCommonKSubstringPred(low, str1, str2)
        invariant forall k :: k >= high ==> !haveCommonKSubstringPred(k, str1, str2)
    {
        var mid := (low + high) / 2;
        if haveCommonKSubstring(mid, str1, str2) {
            low := mid;
        } else {
            high := mid;
        }
    }
    return low;
}
// </vc-code>

