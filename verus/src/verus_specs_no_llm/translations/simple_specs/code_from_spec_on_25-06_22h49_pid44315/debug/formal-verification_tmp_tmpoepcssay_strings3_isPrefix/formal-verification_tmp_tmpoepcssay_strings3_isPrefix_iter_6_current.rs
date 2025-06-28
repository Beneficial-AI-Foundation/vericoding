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
            assert(pre.as_bytes().spec_index(i as int) != str.as_bytes().spec_index(i as int));
            
            // Use the axiom that if bytes differ, the substring is different
            assert(pre != str.spec_index(..pre.len() as int)) by {
                // Proof by contradiction using string indexing axioms
                if pre == str.spec_index(..pre.len() as int) {
                    // If strings are equal, their byte sequences must be equal
                    assert(pre.as_bytes() =~= str.spec_index(..pre.len() as int).as_bytes());
                    // So bytes at position i must be equal
                    assert(pre.as_bytes().spec_index(i as int) == str.spec_index(..pre.len() as int).as_bytes().spec_index(i as int));
                    // By definition of substring, this equals the original string's byte at i
                    assert(str.spec_index(..pre.len() as int).as_bytes().spec_index(i as int) == str.as_bytes().spec_index(i as int));
                    // This contradicts our observation that they differ
                    assert(false);
                }
            }
            
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        
        i += 1;
    }
    
    // After the loop, all bytes match
    assert(i == pre.len());
    assert(pre.len() <= str.len());
    assert(forall|j: int| 0 <= j < pre.len() ==> pre.as_bytes().spec_index(j) == str.as_bytes().spec_index(j));
    
    // Prove string equality from byte equality
    assert(pre == str.spec_index(..pre.len() as int)) by {
        // Two strings are equal if they have the same length and same bytes
        let substr = str.spec_index(..pre.len() as int);
        assert(pre.len() == substr.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> 
            pre.as_bytes().spec_index(j) == substr.as_bytes().spec_index(j)) by {
            assert(forall|j: int| 0 <= j < pre.len() ==> 
                pre.as_bytes().spec_index(j) == str.as_bytes().spec_index(j));
            assert(forall|j: int| 0 <= j < pre.len() ==> 
                substr.as_bytes().spec_index(j) == str.as_bytes().spec_index(j));
        }
        // String equality follows from byte sequence equality
        assert(pre.as_bytes() =~= substr.as_bytes());
    }
    
    assert(isPrefixPred(pre, str));
    return true;
}

}