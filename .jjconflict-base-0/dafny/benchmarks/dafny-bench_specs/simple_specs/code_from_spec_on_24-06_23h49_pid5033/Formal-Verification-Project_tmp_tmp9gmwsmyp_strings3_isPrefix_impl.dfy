//ATOM
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


//ATOM

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//IMPL isPrefix

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
    /* code modified by LLM (iteration 1): fixed missing closing bracket in if condition */
    if |pre| <= |str| && pre == str[..|pre|] {
        res := true;
    } else {
        res := false;
    }
}