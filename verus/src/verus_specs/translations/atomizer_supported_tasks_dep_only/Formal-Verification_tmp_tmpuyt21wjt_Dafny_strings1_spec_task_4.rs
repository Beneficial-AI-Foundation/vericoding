spec fn isPrefixPredicate(pre: &str, str: &str) -> bool
{
    str.len() >= pre.len() && pre <= str
}

pub fn isPrefix(pre: &str, str: &str) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
{
}

spec fn isSubstringPredicate(sub: &str, str: &str) -> bool
{
    str.len() >= sub.len() && (exists|i: usize| 0 <= i <= str.len() && isPrefixPredicate(sub, &str[i..]))
}

pub fn isSubstring(sub: &str, str: &str) -> (res: bool)
    ensures
        res == isSubstringPredicate(sub, str),
{
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: &str, str2: &str) -> bool
{
    str1.len() >= k && str2.len() >= k && (exists|i: usize| 0 <= i <= str1.len() - k && isSubstringPredicate(&(&str1[i..])[..k], str2))
}

pub fn haveCommonKSubstring(k: nat, str1: &str, str2: &str) -> (found: bool)
    ensures
        str1.len() < k || str2.len() < k ==> !found,
        haveCommonKSubstringPredicate(k, str1, str2) == found,
{
}

spec fn maxCommonSubstringPredicate(str1: &str, str2: &str, len: nat) -> bool
{
    forall|k: nat| len < k <= str1.len() ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

pub fn maxCommonSubstringLength(str1: &str, str2: &str) -> (len: nat)
    ensures
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len),
{
}