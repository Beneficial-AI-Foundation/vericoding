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
    
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre.as_bytes().spec_index(j) == str.as_bytes().spec_index(j),
        decreases pre.len() - i
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            // The bytes differ, which means the strings differ at position i
            assert(pre.as_bytes().spec_index(i as int) != str.as_bytes().spec_index(i as int));
            
            // This means the prefix cannot match
            assert(pre != str.spec_index(..pre.len() as int)) by {
                // If they were equal, then all bytes would be equal
                if pre == str.spec_index(..pre.len() as int) {
                    assert(pre.as_bytes().spec_index(i as int) == str.spec_index(..pre.len() as int).as_bytes().spec_index(i as int));
                    // The substring at position i should equal the original string at position i
                    assert(str.spec_index(..pre.len() as int).as_bytes().spec_index(i as int) == str.as_bytes().spec_index(i as int));
                    assert(pre.as_bytes().spec_index(i as int) == str.as_bytes().spec_index(i as int));
                    assert(false); // contradiction
                }
            }
            
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        
        assert(pre.as_bytes().spec_index(i as int) == str.as_bytes().spec_index(i as int));
        i += 1;
    }
    
    // After the loop, we've matched all characters
    assert(i == pre.len());
    assert(pre.len() <= str.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre.as_bytes().spec_index(j) == str.as_bytes().spec_index(j));
    
    // All bytes match, so the strings are equal
    assert(pre == str.spec_index(..pre.len() as int)) by {
        // This follows from the fact that all bytes are equal
        assert(pre.as_bytes() == str.spec_index(..pre.len() as int).as_bytes());
    }
    
    assert(isPrefixPred(pre, str));
    return true;
}

}