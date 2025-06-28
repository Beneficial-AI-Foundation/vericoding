// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len() as int)
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len() as int)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre.spec_index(j) === str.spec_index(j)
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            return false;
        }
        i += 1;
    }
    
    return true;
}

}