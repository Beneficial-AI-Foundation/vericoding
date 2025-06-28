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
    
    // Convert strings to bytes for character-by-character comparison
    let pre_bytes = pre.as_bytes();
    let str_bytes = str.as_bytes();
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            i <= str.len(),
            pre_bytes@ == pre@,
            str_bytes@ == str@,
            forall|j: int| 0 <= j < i ==> pre_bytes@.index(j) == str_bytes@.index(j)
    {
        if pre_bytes[i] != str_bytes[i] {
            // Prove that this means the strings don't match
            assert(pre@.index(i as int) != str@.index(i as int));
            assert(pre@ != str@.subrange(0, pre.len() as int)) by {
                let sub_seq = str@.subrange(0, pre.len() as int);
                assert(pre@.index(i as int) != sub_seq.index(i as int));
            };
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we've checked all characters and they match
    assert(forall|j: int| 0 <= j < pre.len() ==> pre_bytes@.index(j) == str_bytes@.index(j));
    
    // Prove sequence equality
    assert(pre@ == str@.subrange(0, pre.len() as int)) by {
        let sub_seq = str@.subrange(0, pre.len() as int);
        assert(pre@.len() == pre.len());
        assert(sub_seq.len() == pre.len());
        assert(forall|j: int| 0 <= j < pre@.len() ==> pre@.index(j) == sub_seq.index(j)) by {
            assert(forall|j: int| 0 <= j < pre.len() ==> {
                pre_bytes@.index(j) == str_bytes@.index(j) &&
                pre@.index(j) == pre_bytes@.index(j) &&
                str@.index(j) == str_bytes@.index(j) &&
                sub_seq.index(j) == str@.index(j)
            });
        };
    };
    
    assert(isPrefixPred(pre, str));
    return true;
}

}