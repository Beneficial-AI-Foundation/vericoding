predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

// <vc-spec>
method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str|
    {return false;}

  var i := 0;
  while i < |pre|
    decreases |pre| - i
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
  {
    if pre[i] != str[i]
    {
        return false;
    } 
    i := i + 1;
  }
 return true;
}

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

// <vc-helpers>
lemma isPrefixCorrect(sub: string, str: string, i: int)
  requires 0 <= i <= |str|
  requires |str| - i >= |sub|
  ensures isPrefixPredicate(sub, str[i..]) <==> (|sub| <= |str| - i && forall j :: 0 <= j < |sub| ==> sub[j] == str[i + j])
{
  if isPrefixPredicate(sub, str[i..]) {
    assert |str[i..]| >= |sub|;
    assert sub <= str[i..];
    assert forall j :: 0 <= j < |sub| ==> sub[j] == str[i..][j];
    assert forall j :: 0 <= j < |sub| ==> str[i..][j] == str[i + j];
  } else {
    if |sub| <= |str| - i && (forall j :: 0 <= j < |sub| ==> sub[j] == str[i + j]) {
      assert |str[i..]| >= |sub|;
      assert forall j :: 0 <= j < |sub| ==> sub[j] == str[i..][j];
      assert sub <= str[i..];
      assert isPrefixPredicate(sub, str[i..]);
      assert false;
    }
  }
}
// </vc-helpers>

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
// </vc-spec>
// <vc-code>
{
  if |str| < |sub| {
    return false;
  }
  
  var i := 0;
  while i <= |str| - |sub|
    decreases |str| - i
    invariant 0 <= i <= |str| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
  {
    isPrefixCorrect(sub, str, i);
    var prefixRes := isPrefix(sub, str[i..]);
    if prefixRes {
      return true;
    }
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}




predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}