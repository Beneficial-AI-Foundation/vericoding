// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}
spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists |i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.index(i..)))
}

spec fn spec_isPrefix(pre: String, str: String) -> res: bool
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    false
}

}