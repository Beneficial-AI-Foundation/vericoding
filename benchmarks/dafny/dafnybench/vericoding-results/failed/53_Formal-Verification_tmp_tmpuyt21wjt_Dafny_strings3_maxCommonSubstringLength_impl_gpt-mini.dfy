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
// No helper lemmas required for this solution.
// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
  var n := |str1|;
  var m := |str2|;
  var kk := n;
  var found := false;
  var resk := 0;
  var wi := 0;
  var wj := 0;

  // Invariant: for all k' with kk < k' <= n there is no common substring of length k'
  while kk >= 0 && !found
    invariant  -1 <= kk <= n
    invariant forall k' :: kk < k' <= n ==> haveNotCommonKSubstringPred(k', str1, str2)
    decreases kk + 1
  {
    // scan all starting positions i in str1 for current length kk
    var i := 0;
    while i <= n - kk && !found
      invariant 0 <= i <= n - kk + 1
      invariant forall i' :: 0 <= i' < i ==>
                 (forall j' :: 0 <= j' <= m - kk ==> str2[j'..j'+kk] != str1[i'..i'+kk])
      decreases n - i
    {
      var j := 0;
      while j <= m - kk && !found
        invariant 0 <= j <= m - kk + 1
        invariant forall j' :: 0 <= j' < j ==> str2[j'..j'+kk] != str1[i..i+kk]
        decreases m - j
      {
        if str2[j..j+kk] == str1[i..i+kk] {
          // found a common substring of length kk at str1[i..i+kk] and str2[j..j+kk]
          found := true;
          resk := kk;
          wi := i;
          wj := j;
        } else {
          j := j + 1;
        }
      }
      if !found {
        i := i + 1;
      }
    }

    if !found {
      // we have scanned all i (i = n-kk+1), so by the i-loop invariant there is no match for this kk
      assert forall i0 :: 0 <= i0 <= n - kk ==>
                (forall j0 :: 0 <= j0 <= m - kk ==> str2[j0..j0+kk] != str1[i0..i0+kk]);
      // This implies haveNotCommonKSubstringPred(kk, str1, str2)
      assert haveNotCommonKSubstringPred(kk, str1, str2);
      kk := kk - 1;
    }
  }

  // At this point either found=true with witnesses (wi, wj, resk) or kk < 0 and not found.
  if !found {
    // Should not happen because empty substring always matches; nonetheless, set to 0 witnesses.
    resk := 0;
    wi := 0;
    wj := 0;
  }

  // Prove the postconditions:
  // 1) haveCommonKSubstringPred(resk, str1, str2)
  // We provide witnesses i1 = wi, j1 = wi + resk, and show isSubstringPred(str1[wi..wi+resk], str2).
  if resk == 0 {
    // empty substring is always a substring: pick j2 = 0
    // show the slice is empty
    assert wi + resk == wi;
    assert str1[wi..wi+resk] == "";
    assert 0 <= 0 <= m;
    // empty string is a prefix of any string
    assert isPrefixPred("", str2);
    // provide witness j2 = 0
    assert exists j2 :: j2 == 0 && 0 <= j2 <= |str2| && isPrefixPred(str1[wi..wi+resk], str2[j2..]);
    // provide witnesses i1 = 0, j1 = 0 + resk
    assert 0 <= 0 <= n - resk;
    assert exists i1, j1 :: i1 == 0 && j1 == 0 + resk && 0 <= i1 <= |str1| - resk && isSubstringPred(str1[i1..j1], str2);
    assert haveCommonKSubstringPred(resk, str1, str2);
  } else {
    // resk > 0 and found => we recorded matching slices equality
    assert 0 <= wi <= n - resk;
    assert 0 <= wj <= m - resk;
    assert str2[wj..wj+resk] == str1[wi..wi+resk];
    // hence isPrefixPred holds for str2[wj..]
    assert isPrefixPred(str1[wi..wi+resk], str2[wj..]);
    // provide witness j2 = wj for isSubstringPred
    assert exists j2 :: j2 == wj && 0 <= j2 <= |str2| && isPrefixPred(str1[wi..wi+resk], str2[j2..]);
    // provide witnesses i1 = wi, j1 = wi + resk for haveCommonKSubstringPred
    assert exists i1, j1 :: i1 == wi && j1 == wi + resk && 0 <= i1 <= |str1| - resk && isSubstringPred(str1[i1..j1], str2);
    assert haveCommonKSubstringPred(resk, str1, str2);
  }

  // 2) maximality: for all k with resk < k <= |str1|, no common substring of length k.
  // By the outer loop invariant, when we found resk the invariant guarantees for all k' with resk < k' <= n there was no common substring.
  assert forall k' :: resk < k' <= n ==> haveNotCommonKSubstringPred(k', str1, str2);
  // This implies the first postcondition (converting haveNotCommonKSubstringPred to negation of haveCommonKSubstringPred)
  assert forall k' :: resk < k' <= |str1| ==> !haveCommonKSubstringPred(k', str1, str2);

  len := resk;
}
// </vc-code>

