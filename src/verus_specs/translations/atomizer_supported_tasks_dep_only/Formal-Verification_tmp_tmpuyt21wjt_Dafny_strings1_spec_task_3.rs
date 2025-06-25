// ATOM 
pub open spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool
{
  str.len() >= pre.len() && pre <= str
}

// SPEC 
pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
{
}

// ATOM 
pub open spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool
{
  str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)))
}

// SPEC 
pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res == isSubstringPredicate(sub, str),
{
}

// ATOM 
pub open spec fn haveCommonKSubstringPredicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
  str1.len() >= k && str2.len() >= k && (exists|i: int| 0 <= i <= str1.len() - k && isSubstringPredicate((str1.subrange(i as int, str1.len() as int)).subrange(0int, k as int), str2))
}

// SPEC 
pub fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        str1.len() < k || str2.len() < k ==> !found,
        haveCommonKSubstringPredicate(k, str1, str2) == found,
{
}

//ATOM_PLACEHOLDER_maxCommonSubstringPredicate

//ATOM_PLACEHOLDER_maxCommonSubstringLength