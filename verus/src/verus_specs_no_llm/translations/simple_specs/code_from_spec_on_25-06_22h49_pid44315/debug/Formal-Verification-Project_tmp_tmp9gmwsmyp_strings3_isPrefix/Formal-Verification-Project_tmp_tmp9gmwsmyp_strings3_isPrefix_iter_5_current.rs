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
        assert(isNotPrefixPred(pre, str));
        assert(!isPrefixPred(pre, str));
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
            forall|j: int| 0 <= j < i ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j)
    {
        if pre_bytes[i] != str_bytes[i] {
            // At position i, the bytes differ
            assert(pre_bytes.spec_index(i) != str_bytes.spec_index(i));
            
            // This means not all bytes are equal up to pre.len()
            assert(!(forall|j: int| 0 <= j < pre.len() ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j)));
            
            // In Verus, if bytes differ, then the string slice differs
            assert(pre != str.spec_index(..pre.len()));
            assert(isNotPrefixPred(pre, str));
            assert(!isPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    // At this point, all bytes match up to pre.len()
    assert(i == pre.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j));
    
    // In Verus, if all bytes are equal and we have the right length relationship,
    // then the strings are equal. This is built into Verus's understanding of strings.
    assert(pre.as_bytes() == str.spec_index(..pre.len()).as_bytes());
    assert(pre == str.spec_index(..pre.len()));
    assert(isPrefixPred(pre, str));
    assert(!isNotPrefixPred(pre, str));
    
    return true;
}

}