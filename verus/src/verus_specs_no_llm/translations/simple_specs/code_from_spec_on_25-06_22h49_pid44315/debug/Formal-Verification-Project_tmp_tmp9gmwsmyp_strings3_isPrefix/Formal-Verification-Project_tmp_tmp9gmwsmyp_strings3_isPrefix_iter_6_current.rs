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
        assert(!isPrefixPred(pre, str));
        return false;
    }
    
    // Convert to bytes once outside the loop
    let pre_bytes = pre.as_bytes();
    let str_bytes = str.as_bytes();
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j),
            pre_bytes == pre.as_bytes(),
            str_bytes == str.as_bytes()
    {
        if pre_bytes[i] != str_bytes[i] {
            // At position i, the bytes differ
            assert(pre_bytes.spec_index(i as int) != str_bytes.spec_index(i as int));
            
            // This means not all bytes are equal up to pre.len()
            assert(exists|k: int| 0 <= k < pre.len() && pre_bytes.spec_index(k) != str_bytes.spec_index(k));
            
            // Therefore the prefix condition fails
            assert(isNotPrefixPred(pre, str));
            assert(!isPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    // At this point, all bytes match up to pre.len()
    assert(i == pre.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j));
    
    // This establishes that the prefix matches
    assert(pre == str.spec_index(..pre.len() as int)) by {
        // The proof relies on the fact that if two strings have the same bytes,
        // they are equal strings
        assert(pre.as_bytes() == str.spec_index(..pre.len() as int).as_bytes());
    }
    
    assert(isPrefixPred(pre, str));
    assert(!isNotPrefixPred(pre, str));
    
    return true;
}

}