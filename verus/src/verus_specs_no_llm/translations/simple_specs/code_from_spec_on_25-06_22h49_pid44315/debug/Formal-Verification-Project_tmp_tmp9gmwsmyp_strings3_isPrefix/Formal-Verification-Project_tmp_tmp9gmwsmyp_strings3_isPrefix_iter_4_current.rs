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

// Helper lemma to connect byte equality with string equality
proof fn lemma_bytes_eq_implies_string_eq(s1: String, s2: String, len: int)
    requires
        0 <= len <= s1.len(),
        len <= s2.len(),
        forall|i: int| 0 <= i < len ==> s1.as_bytes().spec_index(i) == s2.as_bytes().spec_index(i)
    ensures
        s1.spec_index(..len) == s2.spec_index(..len)
{
    // This lemma establishes that if all bytes match up to len,
    // then the string slices are equal
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
            
            // This means the strings cannot be equal up to pre.len()
            assert(!(forall|j: int| 0 <= j < pre.len() ==> pre_bytes.spec_index(j) == str_bytes.spec_index(j)));
            
            // Therefore pre != str[..pre.len()]
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
    
    // Use the helper lemma to prove string equality
    proof {
        lemma_bytes_eq_implies_string_eq(pre, str, pre.len() as int);
    }
    
    assert(pre == str.spec_index(..pre.len()));
    assert(isPrefixPred(pre, str));
    assert(!isNotPrefixPred(pre, str));
    
    return true;
}

}