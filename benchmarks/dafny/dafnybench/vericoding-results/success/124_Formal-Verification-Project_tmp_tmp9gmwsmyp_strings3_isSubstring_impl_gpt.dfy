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

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i <= |str|
    invariant 0 <= i <= |str| + 1
    invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    decreases |str| + 1 - i
  {
    var r := isPrefix(sub, str[i..]);
    if r {
      res := true;
      return;
    } else {
      assert isNotPrefixPred(sub, str[i..]);
      i := i + 1;
    }
  }

  res := false;

  assert i > |str|;

  forall j | 0 <= j <= |str|
    ensures isNotPrefixPred(sub, str[j..])
  {
    assert i > |str|;
    assert j <= |str|;
    assert j < i;
    assert 0 <= j < i;
    assert isNotPrefixPred(sub, str[j..]);
  }

  assert !isSubstringPred(sub, str);
}
// </vc-code>

