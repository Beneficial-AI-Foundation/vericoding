use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len())
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len())
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
            forall|j: int| 0 <= j < i ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1)
    {
        // Convert to bytes for character-by-character comparison
        let pre_bytes = pre.as_bytes();
        let str_bytes = str.as_bytes();
        
        if pre_bytes[i] != str_bytes[i] {
            return false;
        }
        i += 1;
    }
    
    return true;
}

}