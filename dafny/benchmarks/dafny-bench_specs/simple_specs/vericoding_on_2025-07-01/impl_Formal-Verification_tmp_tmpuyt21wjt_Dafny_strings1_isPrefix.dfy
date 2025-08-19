//ATOM

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