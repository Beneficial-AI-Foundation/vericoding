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
predicate lemma_haveCommonKSubstring_equivalent_predicate(k: nat, str1: string, str2: string)
{
    exists i :: 0 <= i + k <= |str1| && isSubstring(str1[i .. i+k], str2)
}

lemma lemma_isSubstringPred_isSubstring(sub: string, str: string)
  ensures isSubstringPred(sub, str) <==> isSubstring(sub, str)
{
  if isSubstringPred(sub, str) {
    var i: nat := 0;
    while i <= |str|
      invariant 0 <= i <= |str|
      decreases |str| - i
    {
      if isPrefixPred(sub, str[i..]) {
        if |sub| <= |str| - i {
          // If sub is a prefix of str[i..], then str[i..i+|sub|] == sub.
          // We need to show there exists j such that str[j..j+|sub|] == sub.
          // We can pick j = i.
          assert 0 <= i <= |str| - |sub| by {
            if |sub| == 0 { assert 0 <= i <= |str|; }
            else { assert i + |sub| <= |str|; assert i <= |str| - |sub|; }
          }
          assert str[i..i+|sub|] == sub;
          return;
        }
      }
      i := i + 1;
    }
  } else {
    // If !isSubstringPred(sub, str), then forall i, !isPrefixPred(sub, str[i..]).
    // This means forall i, (sub != str[i..|sub|+i] || |sub| > |str|-i).
    // So there is no i such that str[i..i+|sub|] == sub.
  }
}

lemma lemma_haveCommonKSubstring_equivalent(k: nat, str1: string, str2: string)
  ensures haveCommonKSubstringPred(k, str1, str2) <==> lemma_haveCommonKSubstring_equivalent_predicate(k, str1, str2)
{
  calc {
    haveCommonKSubstringPred(k, str1, str2);
    (exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2));
    // Apply lemma_isSubstringPred_isSubstring to the inner predicate
    (exists i1 :: 0 <= i1 <= |str1|- k && isSubstringPred(str1[i1..i1+k],str2));
    (exists i1 :: 0 <= i1 <= |str1|- k && isSubstring(str1[i1..i1+k],str2));
  }
}

// A helper for binary search
function haveCommonKSubstringWrapper(k: nat, str1: string, str2: string): bool
  // No reads clause for functions unless they read mutable state. Strings are immutable.
  ensures haveCommonKSubstringWrapper(k,str1,str2)  <==>  haveCommonKSubstringPred(k,str1,str2)
{
  haveCommonKSubstring(k, str1, str2)
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    // Check that both strings are larger than k 
    if (k == 0) {
        return true;
    }
    if (k > |str1| || k > |str2| ){
        return false;
    }
    
    // Initialize variables
    var i := 0;
    
    // Don't want to exceed the bounds of str1 when checking for the element that is k away
    while i <= |str1|-k
    // Invariant to stay within bounds
    invariant 0 <= i <= (|str1|-k) + 1
    // Invariant to show that when found is true, it is a substring
    invariant found ==> (exists m :: 0 <= m <= (|str1| - k) && isSubstringPred(str1[m..m+k], str2))
    // Invariant to show that when found is false (so far), all checked prefixes are not substrings
    invariant !found ==> (forall m :: (0 <= m < i ) ==> isNotSubstringPred(str1[m..m+k], str2))
    // Telling dafny that i is that value that is increasing
    decreases |str1| - k - i
    {
        lemma_isSubstringPred_isSubstring(str1[i..(i + k)], str2);
        if  isSubstring(str1[i..(i + k)], str2) 
        {
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
    if (|str1| == 0 || |str2| == 0) {
        return 0;
    }

    var low := 0;
    var high := |str1|; // Note: |str1| is an upper bound for the length of a common substring
    var ans := 0;

    // Prove that k=0 always has a common substring
    // This will help with the invariant when mid is 0
    lemma_haveCommonKSubstring_equivalent(0, str1, str2);
    assert haveCommonKSubstringPred(0, str1, str2);


    while low <= high
        invariant 0 <= low <= |str1| + 1
        invariant -1 <= high <= |str1|
        invariant 0 <= ans <= |str1|
        invariant (ans == 0 ==> haveCommonKSubstringPred(0, str1, str2)) // 0 length substring always exists
        invariant (ans > 0 ==> haveCommonKSubstringPred(ans, str1, str2))
        // For any k' > high, there is no common substring of length k'.
        invariant (forall k' :: high < k' <= |str1| ==> !haveCommonKSubstringWrapper(k', str1, str2))
        // If low is advanced, it means all lengths up to low-1 have been checked and if found common,
        // then 'ans' has been updated accordingly.
        // It's not necessarily "all k' up to low have common substring OR k' <= ans"
        // but rather: lengths up to 'ans' have common substring, and from 'ans'+1 to 'low'-1,
        // we've explored without finding new common substrings of maximal length.
        invariant (ans <= low)
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        // ensure mid is within valid range to avoid issues for str1=""
        if (mid > |str1|) { mid := |str1|; } 

        if haveCommonKSubstringWrapper(mid, str1, str2) {
            ans := mid;
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }

    assert haveCommonKSubstringPred(ans, str1, str2);
    assert (forall k :: ans < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2));
    
    return ans;
}
// </vc-code>

