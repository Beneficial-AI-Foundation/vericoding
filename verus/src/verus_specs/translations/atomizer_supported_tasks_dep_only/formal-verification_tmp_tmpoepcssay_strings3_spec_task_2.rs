// ATOM 
spec fn isPrefixPred(pre: String, str: String) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 
spec fn isNotPrefixPred(pre: String, str: String) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

//ATOM_PLACEHOLDER_PrefixNegationLemma

// SPEC 
pub fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures(!res <==> isNotPrefixPred(pre, str))
    ensures(res <==> isPrefixPred(pre, str))
{
}

// ATOM 
spec fn isSubstringPred(sub: String, str: String) -> bool
{
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

// ATOM 
spec fn isNotSubstringPred(sub: String, str: String) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

//ATOM_PLACEHOLDER_SubstringNegationLemma

// SPEC 
pub fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures(res <==> isSubstringPred(sub, str))
    ensures(res ==> isSubstringPred(sub, str))
    // ensures(!res ==> !isSubstringPred(sub, str))
    ensures(isSubstringPred(sub, str) ==> res)
    ensures(isSubstringPred(sub, str) ==> res)
    ensures(!res <==> isNotSubstringPred(sub, str)) // This postcondition follows from the above lemma.
{
}

//ATOM_PLACEHOLDER_haveCommonKSubstringPred

//ATOM_PLACEHOLDER_haveNotCommonKSubstringPred

//ATOM_PLACEHOLDER_commonKSubstringLemma

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_maxCommonSubstringLength