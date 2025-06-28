use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre@ == str@.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre@ != str@.subrange(0, pre.len() as int)
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
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            i <= str.len(),
            forall|j: int| 0 <= j < i ==> pre@.index(j) == str@.index(j)
    {
        // Compare characters directly using string indexing
        let pre_char = pre@.index(i as int);
        let str_char = str@.index(i as int);
        
        if pre_char != str_char {
            assert(pre@.index(i as int) != str@.index(i as int));
            assert(pre@ != str@.subrange(0, pre.len() as int)) by {
                let sub_seq = str@.subrange(0, pre.len() as int);
                assert(pre@.index(i as int) != sub_seq.index(i as int));
                // Since sequences differ at position i, they are not equal
                assert(pre@.len() == sub_seq.len());
                assert(exists|k: int| 0 <= k < pre@.len() && pre@.index(k) != sub_seq.index(k));
            };
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we've checked all characters and they match
    assert(forall|j: int| 0 <= j < pre.len() ==> pre@.index(j) == str@.index(j));
    
    // Prove sequence equality
    assert(pre@ == str@.subrange(0, pre.len() as int)) by {
        let sub_seq = str@.subrange(0, pre.len() as int);
        assert(pre@.len() == pre.len());
        assert(sub_seq.len() == pre.len());
        assert(forall|j: int| 0 <= j < pre@.len() ==> pre@.index(j) == sub_seq.index(j)) by {
            assert(forall|j: int| 0 <= j < pre.len() ==> {
                pre@.index(j) == str@.index(j) &&
                sub_seq.index(j) == str@.index(j)
            });
        };
        // Two sequences are equal if they have the same length and same elements
        assert(pre@.ext_equal(sub_seq));
    };
    
    assert(isPrefixPred(pre, str));
    return true;
}

}