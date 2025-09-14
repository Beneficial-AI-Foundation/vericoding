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
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
  var best := 0;
  // prove haveCommonKSubstringPred(0, str1, str2)
  // witness i1 = 0, j1 = 0 and i2 = 0 for isSubstringPred("", str2)
  assert exists i2 :: i2 == 0 && 0 <= i2 <= |str2| && isPrefixPred(str1[0..0], str2[i2..]);
  assert exists i1, j1 :: i1 == 0 && j1 == 0 && 0 <= i1 <= |str1| - 0 && isSubstringPred(str1[i1..j1], str2);

  var k := 1;
  while k <= |str1|
    invariant 0 <= best < k <= |str1| + 1
    invariant haveCommonKSubstringPred(best, str1, str2)
    invariant forall kk :: best < kk < k ==> haveNotCommonKSubstringPred(kk, str1, str2)
  {
    var found := false;
    var found_i1 := 0;
    var found_i2 := 0;

    var i1 := 0;
    while !found && i1 <= |str1| - k
      invariant 0 <= i1 <= |str1| - k + 1
      invariant forall j1 :: 0 <= j1 < i1 ==> forall j2 :: 0 <= j2 <= |str2| - k ==> str1[j1..j1+k] != str2[j2..j2+k]
    {
      var i2 := 0;
      while !found && i2 <= |str2| - k
        invariant 0 <= i2 <= |str2| - k + 1
        invariant forall j2 :: 0 <= j2 < i2 ==> str1[i1..i1+k] != str2[j2..j2+k]
      {
        if str1[i1..i1+k] == str2[i2..i2+k] {
          found := true;
          found_i1 := i1;
          found_i2 := i2;
        } else {
          i2 := i2 + 1;
        }
      }
      if !found {
        i1 := i1 + 1;
      }
    }

    if found {
      // Provide witnesses to show haveCommonKSubstringPred(k, str1, str2)
      // Witness i1 = found_i1, j1 = found_i1 + k
      // Show isSubstringPred(str1[found_i1..found_i1+k], str2) by witnessing found_i2
      assert 0 <= found_i1 <= |str1| - k;
      assert 0 <= found_i2 <= |str2| - k;
      assert str1[found_i1..found_i1+k] == str2[found_i2..found_i2+k];
      // isPrefixPred holds for the chosen i2
      assert k <= |str2| - found_i2;
      assert isPrefixPred(str1[found_i1..found_i1+k], str2[found_i2..]);
      assert exists i2 :: i2 == found_i2 && 0 <= i2 <= |str2| && isPrefixPred(str1[found_i1..found_i1+k], str2[i2..]);
      assert exists i1a, j1a :: i1a == found_i1 && j1a == found_i1 + k && 0 <= i1a <= |str1| - k && isSubstringPred(str1[i1a..j1a], str2);

      best := k;
    } else {
      // No substring of length k found: prove haveNotCommonKSubstringPred(k, str1, str2)
      // From the outer i1-loop completion we know that for all i1 in 0..|str1|-k, and for all i2 in 0..|str2|-k,
      // str1[i1..i1+k] != str2[i2..i2+k]. Thus each str1[i1..i1+k] is not a substring of str2.
      assert forall i1a :: 0 <= i1a <= |str1| - k ==>
        (forall i2a :: 0 <= i2a <= |str2| - k ==> str1[i1a..i1a+k] != str2[i2a..i2a+k]);
      // From this, for every i1a we have isNotSubstringPred(str1[i1a..i1a+k], str2)
      assert forall i1a :: 0 <= i1a <= |str1| - k ==>
        isNotSubstringPred(str1[i1a..i1a+k], str2);
      // Therefore haveNotCommonKSubstringPred(k, str1, str2)
      assert haveNotCommonKSubstringPred(k, str1, str2);
    }

    k := k + 1;
  }

  len := best;
}
// </vc-code>

