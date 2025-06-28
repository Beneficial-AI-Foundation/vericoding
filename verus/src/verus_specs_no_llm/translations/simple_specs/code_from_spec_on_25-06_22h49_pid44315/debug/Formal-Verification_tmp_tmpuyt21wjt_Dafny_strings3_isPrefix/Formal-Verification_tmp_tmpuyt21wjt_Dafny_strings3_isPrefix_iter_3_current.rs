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
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            i <= str.len(),
            forall|j: int| 0 <= j < i ==> pre@.index(j) == str@.index(j)
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        let pre_seq = pre@;
        let str_subrange = str@.subrange(0, pre.len() as int);
        
        assert(pre_seq.len() == pre.len());
        assert(str_subrange.len() == pre.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> pre_seq.index(j) == str@.index(j));
        assert(forall|j: int| 0 <= j < pre.len() ==> str_subrange.index(j) == str@.index(j));
        
        assert(pre_seq =~= str_subrange) by {
            assert(pre_seq.len() == str_subrange.len());
            assert(forall|j: int| 0 <= j < pre_seq.len() ==> pre_seq.index(j) == str_subrange.index(j)) by {
                assert(forall|j: int| 0 <= j < pre.len() ==> pre_seq.index(j) == str@.index(j));
                assert(forall|j: int| 0 <= j < pre.len() ==> str_subrange.index(j) == str@.index(j));
            }
        }
    }
    
    return true;
}

}