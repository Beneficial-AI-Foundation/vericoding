use vstd::prelude::*;

verus! {

// ATOM 
spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool
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
spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool
{
    str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.subrange(i, str.len() as int)))
}

// SPEC 
pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res == isSubstringPredicate(sub, str),
{
}

// ATOM 
spec fn haveCommonKSubstringPredicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
    str1.len() >= k && str2.len() >= k && (exists|i: int| 0 <= i <= str1.len() - k && isSubstringPredicate(str1.subrange(i, str1.len() as int).subrange(0, k as int), str2))
}

// SPEC 
pub fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        str1.len() < k || str2.len() < k ==> !found,
        haveCommonKSubstringPredicate(k, str1, str2) == found,
{
}

// ATOM 
spec fn maxCommonSubstringPredicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool
{
    forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPredicate(k as nat, str1, str2)
}

// SPEC 
pub fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    ensures
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len),
{
}

}