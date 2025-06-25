// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}
spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists i :: 0 <= i <= str.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}
spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && (exists i :: 0 <= i <= str1.len() - k && isSubstringPredicate((str1.spec_index(i..))[..k], str2))
}
spec fn maxCommonSubstringPredicate(str1: String, str2: String, len: nat) -> bool {
    forall k :: len < k <= str1.len() ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    return false;
}

}