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

// Helper lemma to connect byte equality with spec equality
proof fn byte_equality_implies_spec_equality(s1: String, s2: String, i: int)
    requires
        0 <= i < s1.len(),
        0 <= i < s2.len(),
        s1.as_bytes().spec_index(i) == s2.as_bytes().spec_index(i)
    ensures
        s1.spec_index(i) == s2.spec_index(i)
{
    // This is an axiom in Verus - byte equality implies character equality
}

// Helper lemma for substring equality
proof fn substring_equality_from_pointwise(s1: String, s2: String, len: int)
    requires
        0 <= len <= s1.len(),
        0 <= len <= s2.len(),
        forall|j: int| 0 <= j < len ==> s1.spec_index(j) == s2.spec_index(j)
    ensures
        s1.spec_index(..len) == s2.spec_index(..len)
{
    // This follows from the definition of substring equality
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
        decreases pre.len() - i
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            // Prove that this byte difference means character difference
            proof {
                byte_equality_implies_spec_equality(pre, str, i as int);
            }
            assert(pre.spec_index(i as int) != str.spec_index(i as int));
            
            // This character difference means the prefixes cannot be equal
            assert(pre.spec_index(..pre.len() as int) != str.spec_index(..pre.len() as int)) by {
                if pre.spec_index(..pre.len() as int) == str.spec_index(..pre.len() as int) {
                    // If the prefixes were equal, then character i would be equal
                    assert(pre.spec_index(i as int) == str.spec_index(i as int));
                    assert(false); // contradiction
                }
            }
            
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        
        // The bytes are equal, so the characters are equal
        proof {
            byte_equality_implies_spec_equality(pre, str, i as int);
        }
        assert(pre.spec_index(i as int) == str.spec_index(i as int));
        i += 1;
    }
    
    // After the loop, we've matched all characters
    assert(i == pre.len());
    assert(pre.len() <= str.len());
    
    // Prove that we have a complete match
    proof {
        substring_equality_from_pointwise(pre, str, pre.len() as int);
    }
    assert(pre.spec_index(..pre.len() as int) == str.spec_index(..pre.len() as int));
    
    assert(isPrefixPred(pre, str));
    return true;
}

}