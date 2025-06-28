// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && str.subrange(0, pre.len() as int) == pre
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    // Check if the first pre.len() characters of str match pre
    let prefix_part = str.subrange(0, pre.len() as int);
    return prefix_part == pre;
}

}