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
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre.get_char(j) == str.get_char(j),
    {
        if pre.get_char(i as int) != str.get_char(i as int) {
            assert(pre != str.spec_index(..pre.len() as int)) by {
                let j = i as int;
                assert(pre.get_char(j) != str.get_char(j));
                assert(pre.get_char(j) != str.spec_index(..pre.len() as int).get_char(j));
            };
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < pre.len() ==> pre.get_char(j) == str.get_char(j));
    
    assert(pre == str.spec_index(..pre.len() as int)) by {
        assert(pre.len() == str.spec_index(..pre.len() as int).len());
        assert(forall|j: int| 0 <= j < pre.len() ==> 
            pre.get_char(j) == str.spec_index(..pre.len() as int).get_char(j));
    };
    
    assert(isPrefixPred(pre, str));
    return true;
}

}