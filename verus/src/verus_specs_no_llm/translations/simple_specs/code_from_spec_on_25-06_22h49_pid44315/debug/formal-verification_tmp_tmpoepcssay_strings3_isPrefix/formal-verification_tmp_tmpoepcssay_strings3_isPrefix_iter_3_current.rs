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
            forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j),
            pre.spec_index(..i as int) == str.spec_index(..i as int)
        decreases pre.len() - i
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            // Prove that this character difference means the strings are not equal
            assert(pre.spec_index(i as int) != str.spec_index(i as int));
            
            // Use proof by contradiction to show pre != str.spec_index(..pre.len() as int)
            assert(pre.spec_index(..pre.len() as int) != str.spec_index(..pre.len() as int)) by {
                // If they were equal, then character at position i would be equal
                if pre.spec_index(..pre.len() as int) == str.spec_index(..pre.len() as int) {
                    assert(pre.spec_index(i as int) == str.spec_index(i as int));
                    assert(false); // contradiction
                }
            }
            
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        
        // Prove that this character match extends our prefix match
        assert(pre.spec_index(i as int) == str.spec_index(i as int));
        i += 1;
    }
    
    // After the loop, we've matched all characters
    assert(i == pre.len());
    assert(pre.len() <= str.len());
    
    // Prove that we have a complete match
    assert(pre.spec_index(..pre.len() as int) == str.spec_index(..pre.len() as int)) by {
        // This follows from the loop invariant when i == pre.len()
        assert(forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j) == str.spec_index(j));
    }
    
    assert(isPrefixPred(pre, str));
    return true;
}

}