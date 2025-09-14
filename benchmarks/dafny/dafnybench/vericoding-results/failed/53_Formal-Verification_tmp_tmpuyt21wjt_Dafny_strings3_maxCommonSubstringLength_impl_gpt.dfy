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
lemma EmptyIsPrefix(s: string)
  ensures isPrefixPred("", s)
{
  assert |""| == 0;
  assert 0 <= |s|;
  assert s[..0] == "";
}

lemma HaveCommonZeroSubstring(str1: string, str2: string)
  ensures haveCommonKSubstringPred(0, str1, str2)
{
  assert exists i1, j1 ::
           0 <= i1 <= |str1| - 0 && j1 == i1 + 0 && isSubstringPred(str1[i1..j1], str2) by {
    assert 0 <= 0 <= |str1|;
    assert str1[0..0] == "";
    assert isSubstringPred(str1[0..0], str2) by {
      assert 0 <= 0 <= |str2|;
      assert isPrefixPred(str1[0..0], str2[0..]) by {
        assert |str1[0..0]| == 0;
        assert 0 <= |str2[0..]|;
        assert str2[0..][..0] == "";
        assert str1[0..0] == "";
      }
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
  var k: nat := |str1|;
  while k > 0
    invariant k <= |str1|
    invariant forall kk ::
                {:trigger haveCommonKSubstringPred(kk, str1, str2)}
                k < kk <= |str1| ==> !haveCommonKSubstringPred(kk, str1, str2)
    decreases k
  {
    var r := haveCommonKSubstring(k, str1, str2);
    if r {
      len := k;
      return;
    }
    k := k - 1;
  }
  HaveCommonZeroSubstring(str1, str2);
  len := 0;
}
// </vc-code>

