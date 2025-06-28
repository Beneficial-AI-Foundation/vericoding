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
        assert(pre@ == str@.subrange(0, pre.len() as int)) by {
            assert(pre@.len() == pre.len());
            assert(forall|j: int| 0 <= j < pre.len() ==> pre@.index(j) == str@.index(j));
            assert(str@.subrange(0, pre.len() as int).len() == pre.len());
            assert(forall|j: int| 0 <= j < pre.len() ==> 
                pre@.index(j) == str@.subrange(0, pre.len() as int).index(j));
        }
    }
    
    return true;
}

}