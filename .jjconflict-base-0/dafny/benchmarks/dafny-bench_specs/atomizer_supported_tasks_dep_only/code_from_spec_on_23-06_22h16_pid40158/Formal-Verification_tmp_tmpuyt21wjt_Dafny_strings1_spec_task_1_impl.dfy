// ATOM 
predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

// IMPL 
method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str| {
    res := false;
  } else {
    res := pre <= str;
  }
}

//ATOM_PLACEHOLDER_isSubstringPredicate

//ATOM_PLACEHOLDER_isSubstring

//ATOM_PLACEHOLDER_haveCommonKSubstringPredicate

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength