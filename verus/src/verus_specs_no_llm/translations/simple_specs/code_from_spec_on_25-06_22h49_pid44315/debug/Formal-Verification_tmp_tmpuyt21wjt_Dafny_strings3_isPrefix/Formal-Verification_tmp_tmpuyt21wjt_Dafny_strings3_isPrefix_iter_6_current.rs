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
        // Work with character sequences directly
        let pre_seq = pre@;
        let str_seq = str@;
        
        if pre_seq.index(i as int) != str_seq.index(i as int) {
            proof {
                assert(pre@.index(i as int) != str@.index(i as int));
                assert(isNotPrefixPred(pre, str));
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        // At this point, we've checked all characters and they match
        assert(forall|j: int| 0 <= j < pre.len() ==> pre@.index(j) == str@.index(j));
        
        // Now we need to show that pre@ == str@.subrange(0, pre.len() as int)
        let pre_seq = pre@;
        let str_prefix = str@.subrange(0, pre.len() as int);
        
        // Both sequences have the same length
        assert(pre_seq.len() == pre.len());
        assert(str_prefix.len() == pre.len()) by {
            assert(str@.len() >= pre.len());
        }
        
        // All corresponding elements are equal
        assert(forall|j: int| 0 <= j < pre.len() ==> {
            pre_seq.index(j) == str_prefix.index(j)
        }) by {
            assert(forall|j: int| 0 <= j < pre.len() ==> {
                str_prefix.index(j) == str@.index(0 + j)
            });
            assert(forall|j: int| 0 <= j < pre.len() ==> {
                pre_seq.index(j) == str@.index(j)
            });
        }
        
        // Therefore the sequences are equal
        assert(pre_seq.ext_equal(str_prefix));
        assert(pre@ == str@.subrange(0, pre.len() as int));
        assert(isPrefixPred(pre, str));
    }
    
    return true;
}

}