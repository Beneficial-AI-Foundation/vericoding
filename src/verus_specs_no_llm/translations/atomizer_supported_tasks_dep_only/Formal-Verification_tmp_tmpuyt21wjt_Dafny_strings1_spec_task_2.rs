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

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures pre.len() > str.len() ==> !res,
            res == isPrefixPredicate(pre, str)
{
}

}