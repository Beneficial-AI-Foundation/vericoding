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
    
    // Use string slicing directly instead of byte comparison
    let prefix_slice = str.spec_index(..pre.len() as int);
    
    // For the actual implementation, we need to check character by character
    // but we'll use a different approach that Verus can verify
    let pre_chars = pre.as_bytes();
    let str_chars = str.as_bytes();
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre_chars[j] == str_chars[j],
    {
        if pre_chars[i] != str_chars[i] {
            // Prove that if any character doesn't match, the strings aren't equal
            assert(pre != str.spec_index(..pre.len() as int)) by {
                // The byte arrays differ, so the strings must differ
                assert(pre_chars != str_chars.spec_index(..pre.len() as int));
            };
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    // All characters matched - prove the strings are equal
    assert(forall|j: int| 0 <= j < pre.len() ==> pre_chars[j] == str_chars[j]);
    
    // Since all bytes match and lengths are equal for the prefix portion,
    // the prefix equals the corresponding slice of str
    assert(pre == str.spec_index(..pre.len() as int)) by {
        // All corresponding bytes are equal, so the strings are equal
        assert(pre_chars == str_chars.spec_index(..pre.len() as int));
    };
    
    assert(isPrefixPred(pre, str));
    return true;
}

}