// ATOM 
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


// ATOM 

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM_PLACEHOLDER_PrefixNegationLemma

//IMPL 

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
    if |pre| > |str| {
        res := false;
    } else {
        res := (pre == str[..|pre|]);
    }
}

//ATOM_PLACEHOLDER_isSubstringPred

//ATOM_PLACEHOLDER_isNotSubstringPred

//ATOM_PLACEHOLDER_SubstringNegationLemma

//ATOM_PLACEHOLDER_isSubstring


//ATOM_PLACEHOLDER_haveCommonKSubstringPred

//ATOM_PLACEHOLDER_haveNotCommonKSubstringPred

//ATOM_PLACEHOLDER_commonKSubstringLemma

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_haveCommon0SubstringLemma

//ATOM_PLACEHOLDER_maxCommonSubstringLength