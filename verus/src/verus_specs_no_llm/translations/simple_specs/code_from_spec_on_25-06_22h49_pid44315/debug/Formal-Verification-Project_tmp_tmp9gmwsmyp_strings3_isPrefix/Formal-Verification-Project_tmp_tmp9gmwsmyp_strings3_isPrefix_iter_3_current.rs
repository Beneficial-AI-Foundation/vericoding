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
    
    // Convert to bytes once outside the loop
    let pre_bytes = pre.as_bytes();
    let str_bytes = str.as_bytes();
    
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j),
            forall|j: int| 0 <= j < i ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1)
    {
        if pre_bytes[i] != str_bytes[i] {
            // Prove that the prefix doesn't match at position i
            assert(pre_bytes.spec_index(i) != str_bytes.spec_index(i));
            assert(pre.spec_index(i..i+1) != str.spec_index(i..i+1));
            assert(pre != str.spec_index(..pre.len()));
            return false;
        }
        i += 1;
    }
    
    // At this point, all characters match
    assert(i == pre.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1));
    assert(pre == str.spec_index(..pre.len()));
    
    return true;
}

}