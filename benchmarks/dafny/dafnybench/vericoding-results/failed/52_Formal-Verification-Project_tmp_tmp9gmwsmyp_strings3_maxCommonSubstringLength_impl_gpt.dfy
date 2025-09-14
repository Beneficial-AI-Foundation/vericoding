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
lemma EmptyIsPrefix(s: string) ensures isPrefixPred("", s) { }

lemma EmptyIsSubstring(s: string) ensures isSubstringPred("", s)
{
  // Witness i := 0
  assert 0 <= 0 <= |s|;
  EmptyIsPrefix(s[0..]);
  assert isPrefixPred("", s[0..]);
  assert exists i :: 0 <= i <= |s| && isPrefixPred("", s[i..]);
}

lemma HaveCommonKSubstringZero(s1: string, s2: string) ensures haveCommonKSubstringPred(0, s1, s2)
{
  // Show that the empty string is a substring of s2
  EmptyIsSubstring(s2);
  assert isSubstringPred("", s2);

  // Witness i1 := 0, j1 := 0
  assert 0 <= 0 <= |s1|;
  assert s1[0..0] == "";
  assert isSubstringPred(s1[0..0], s2);

  assert exists i1, j1 :: 0 <= i1 <= |s1| - 0 && j1 == i1 + 0 && isSubstringPred(s1[i1..j1], s2) by {
    assert 0 <= 0 <= |s1|;
    assert 0 == 0 + 0;
    assert isSubstringPred(s1[0..0], s2);
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
  var k := |str1|;
  while k > 0
    invariant 0 <= k <= |str1|
    invariant forall kk :: k < kk <= |str1| ==> !haveCommonKSubstringPred(kk, str1, str2)
    decreases k
  {
    var found := haveCommonKSubstring(k, str1, str2);
    if found {
      return k;
    }
    k := k - 1;
  }
  HaveCommonKSubstringZero(str1, str2);
  return 0;
}
// </vc-code>

