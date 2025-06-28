use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && str.subrange(0, pre.len() as int) == pre
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    // Check each character of the prefix
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str[j] == pre[j]
    {
        if str[i] != pre[i] {
            return false;
        }
        i += 1;
    }
    
    return true;
}

}