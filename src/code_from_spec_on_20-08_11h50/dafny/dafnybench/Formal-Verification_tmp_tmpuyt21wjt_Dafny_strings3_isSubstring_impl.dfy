predicate isPrefixPred(sub: string, str: string)
{
    |sub| <= |str| && str[..|sub|] == sub
}

predicate isSubstringPred(sub:string, str:string)
{
    (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}