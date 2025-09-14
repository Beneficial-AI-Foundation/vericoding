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
lemma PrefixFromSlice(sub:string, str:string, i:int)
  requires 0 <= i <= |str|
  requires i + |sub| <= |str|
  requires sub == str[i..i+|sub|]
  ensures isPrefixPred(sub, str[i..])
{
  // length of suffix
  assert |str[i..]| == |str| - i;
  // bound on sub length
  assert |sub| <= |str| - i;
  assert |sub| <= |str[i..]|;
  // slicing relation: (str[i..])[..|sub|] == str[i..i+|sub|]
  assert (str[i..])[..|sub|] == str[i..i+|sub|];
  // hence sub is prefix of str[i..]
  assert sub == (str[i..])[..|sub|];
}
// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
  var n := |str|;
  var i := 0;
  res := false;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant (exists j :: 0 <= j < i && isPrefixPred(sub, str[j..])) <==> res
    decreases n + 1 - i
  {
    if i + |sub| <= n && sub == str[i..i + |sub|] {
      // establish that sub is a prefix of str[i..], then witness existence for postcondition
      PrefixFromSlice(sub, str, i);
      assert 0 <= i <= n;
      assert isPrefixPred(sub, str[i..]);
      res := true;
      assert exists j :: 0 <= j <= n && isPrefixPred(sub, str[j..]);
      return;
    }
    i := i + 1;
  }
  return;
}
// </vc-code>

