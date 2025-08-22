// ATOM 
predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

//IMPL isPrefix
method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
  } else {
    res := (pre <= str);
  }
}

// ATOM 
predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

//IMPL isSubstring
method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  if |str| < |sub| {
    res := false;
  } else {
    res := false;
    var i := 0;
    while i <= |str| - |sub|
      invariant 0 <= i <= |str| - |sub| + 1
      invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
    {
      if sub <= str[i..] {
        res := true;
        break;
      }
      i := i + 1;
    }
  }
}

//ATOM_PLACEHOLDER_haveCommonKSubstringPredicate

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength