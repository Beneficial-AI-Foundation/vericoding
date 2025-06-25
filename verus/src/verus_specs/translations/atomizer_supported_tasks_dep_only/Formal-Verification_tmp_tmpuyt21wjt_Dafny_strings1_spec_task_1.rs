// ATOM 
pub open spec fn isPrefixPredicate(pre: &str, str: &str) -> bool
{
  str.len() >= pre.len() && pre <= str
}


// SPEC 

pub fn isPrefix(pre: &str, str: &str) -> (res: bool)
    ensures(pre.len() > str.len() ==> !res)
    ensures(res == isPrefixPredicate(pre, str))
{
}


//ATOM_PLACEHOLDER_isSubstringPredicate

//ATOM_PLACEHOLDER_isSubstring

//ATOM_PLACEHOLDER_haveCommonKSubstringPredicate


//ATOM_PLACEHOLDER_haveCommonKSubstring


//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength