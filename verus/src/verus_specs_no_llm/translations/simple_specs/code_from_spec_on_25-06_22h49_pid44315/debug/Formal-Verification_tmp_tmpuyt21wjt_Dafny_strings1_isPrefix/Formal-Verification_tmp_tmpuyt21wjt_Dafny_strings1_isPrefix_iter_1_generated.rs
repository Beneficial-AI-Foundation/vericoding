// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    // Check if pre is lexicographically <= str and has the right length relationship
    // This matches the specification's use of pre <= str
    return pre <= str;
}

}