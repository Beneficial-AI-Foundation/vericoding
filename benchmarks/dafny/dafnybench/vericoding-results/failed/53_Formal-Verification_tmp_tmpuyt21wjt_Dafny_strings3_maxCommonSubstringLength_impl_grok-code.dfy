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
method isPrefix(pre: string, str: string) returns (is: bool)
  ensures is <==> isPrefixPred(pre, str)
{
  if |pre| > |str| { return false; }
  for i := 0 to |pre| - 1
    if pre[i] != str[i] { return false; }
  return true;
}

method isSubstring(sub: string, str: string) returns (found: bool)
  ensures found <==> isSubstringPred(sub, str)
{
  if |sub| == 0 { return true; }
  for i := 0 to |str| - |sub|
    if isPrefix(sub, str[i..]) { return true; }
  return false;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
  if k > |str1| { return false; }
  for i := 0 to |str1| - k
    if isSubstring(str1[i..i + k], str2) { return true; }
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
  var len := |str1|;
  while len > 0
    invariant 0 <= len <= |str1|
    invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    decreases len
  {
    var found := haveCommonKSubstring(len, str1, str2);
    if found {
      return len;
    } else {
      len := len - 1;
    }
  }
  return len;
}
// </vc-code>

