// ATOM 
predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}


// SPEC 

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
}


// ATOM 

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


// SPEC 

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
}


//ATOM_PLACEHOLDER_haveCommonKSubstringPredicate


//ATOM_PLACEHOLDER_haveCommonKSubstring


//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength

