// ATOM 
spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 
spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

//ATOM_PLACEHOLDER_PrefixNegationLemma

// SPEC 
pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
}

//ATOM_PLACEHOLDER_isSubstringPred

//ATOM_PLACEHOLDER_isNotSubstringPred

//ATOM_PLACEHOLDER_SubstringNegationLemma

//ATOM_PLACEHOLDER_isSubstring

//ATOM_PLACEHOLDER_haveCommonKSubstringPred

//ATOM_PLACEHOLDER_haveNotCommonKSubstringPred

//ATOM_PLACEHOLDER_commonKSubstringLemma

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_maxCommonSubstringLength