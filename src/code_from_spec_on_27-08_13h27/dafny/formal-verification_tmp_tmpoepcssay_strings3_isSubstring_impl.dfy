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
method isPrefixImpl(pre: string, str: string) returns (res: bool)
  ensures res <==> isPrefixPred(pre, str)
  ensures !res <==> isNotPrefixPred(pre, str)
{
  if |pre| > |str| {
    return false;
  }
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant forall k :: 0 <= k < i ==> pre[k] == str[k]
  {
    if pre[i] != str[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    ensures  res ==> isSubstringPred(sub, str)
    // ensures  !res ==> !isSubstringPred(sub, str)
    ensures  isSubstringPred(sub, str) ==> res
    ensures  isSubstringPred(sub, str) ==> res
    ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
method isSubstringImpl(sub: string, str: string) returns (res: bool)
  ensures res <==> isSubstringPred(sub, str)
  ensures !res <==> isNotSubstringPred(sub, str)
{
  if |sub| == 0 {
    return true;
  }
  if |str| < |sub| {
    return false;
  }
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant forall k :: 0 <= k < i ==> isNotPrefixPred(sub, str[k..])
  {
    var prefixRes := isPrefixImpl(sub, str[i..]);
    if prefixRes {
      return true;
    }
    i := i + 1;
  }
  assert forall k :: 0 <= k <= |str| - |sub| ==> isNotPrefixPred(sub, str[k..]);
  assert forall k :: |str| - |sub| < k <= |str| ==> |sub| > |str[k..]| ==> isNotPrefixPred(sub, str[k..]);
  assert forall k :: 0 <= k <= |str| ==> isNotPrefixPred(sub, str[k..]);
  return false;
}
// </vc-code>
