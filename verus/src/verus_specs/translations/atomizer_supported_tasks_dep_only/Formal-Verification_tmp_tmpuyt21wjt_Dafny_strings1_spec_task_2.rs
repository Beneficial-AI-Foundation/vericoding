// ATOM 
pub open spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool
{
  str.len() >= pre.len() && pre <= str
}


// SPEC 

pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
  ensures(pre.len() > str.len() ==> !res)
  ensures(res == isPrefixPredicate(pre, str))
{
}


// ATOM 

pub open spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool
{
  str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.subrange(i, str.len() as int)))
}


// SPEC 

pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
  ensures(res == isSubstringPredicate(sub, str))
{
}


//ATOM_PLACEHOLDER_haveCommonKSubstringPredicate


//ATOM_PLACEHOLDER_haveCommonKSubstring


//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength