//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}

//IMPL 
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