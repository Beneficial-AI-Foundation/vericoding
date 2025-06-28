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
        let pre_bytes = pre.as_bytes();
        let str_bytes = str.as_bytes();
        
        if pre_bytes[i] != str_bytes[i] {
            assert(pre@.index(i as int) != str@.index(i as int));
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i = i + 1;
    }
    
    proof {
        let pre_seq = pre@;
        let str_subrange = str@.subrange(0, pre.len() as int);
        
        assert(pre_seq.len() == pre.len());
        assert(str_subrange.len() == pre.len());
        
        // Establish that all characters match
        assert(forall|j: int| 0 <= j < pre.len() ==> pre_seq.index(j) == str@.index(j));
        
        // Show that str_subrange has the same characters as the prefix of str
        assert(forall|j: int| 0 <= j < pre.len() ==> str_subrange.index(j) == str@.index(j)) by {
            assert(forall|j: int| 0 <= j < str_subrange.len() ==> 
                str_subrange.index(j) == str@.index(j + 0));
        }
        
        // Combine to show sequences are equal
        assert(pre_seq =~= str_subrange) by {
            assert(pre_seq.len() == str_subrange.len());
            assert(forall|j: int| 0 <= j < pre_seq.len() ==> 
                pre_seq.index(j) == str_subrange.index(j)) by {
                assert(forall|j: int| 0 <= j < pre.len() ==> 
                    pre_seq.index(j) == str@.index(j));
                assert(forall|j: int| 0 <= j < pre.len() ==> 
                    str_subrange.index(j) == str@.index(j));
            }
        }
        
        assert(isPrefixPred(pre, str));
    }
    
    return true;
}

}