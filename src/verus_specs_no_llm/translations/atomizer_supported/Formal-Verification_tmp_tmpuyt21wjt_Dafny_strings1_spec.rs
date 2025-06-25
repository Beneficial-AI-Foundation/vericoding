// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() and pre <= str
}
spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() and (exists|i: int| 0 <= i <= str.len() and isPrefixPredicate(sub, str[i..]))
}
spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k and str2.len() >= k and (exists|i: int| 0 <= i <= str1.len() - k and isSubstringPredicate((str1[i..])[..k], str2))
}
spec fn maxCommonSubstringPredicate(str1: String, str2: String, len: nat) -> bool {
    forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures pre.len() > str.len() ==> !res,
            res == isPrefixPredicate(pre, str)
{
}

}