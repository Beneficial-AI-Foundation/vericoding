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
        assert(isNotPrefixPred(pre, str));
        return false;
    }
    
    // Compare characters byte by byte
    let pre_bytes = pre.as_bytes();
    let str_bytes = str.as_bytes();
    
    let mut i = 0;
    while i < pre.len()
        invariant
            i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre_bytes[j] == str_bytes[j]
    {
        if pre_bytes[i] != str_bytes[i] {
            assert(pre != str.spec_index(..pre.len() as int));
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    // All characters matched
    assert(forall|j: int| 0 <= j < pre.len() ==> pre_bytes[j] == str_bytes[j]);
    assert(pre == str.spec_index(..pre.len() as int));
    assert(isPrefixPred(pre, str));
    return true;
}

}