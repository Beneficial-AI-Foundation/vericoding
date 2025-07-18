use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && str.subrange(0, pre.len() as int) == pre
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    // Check each character of the prefix
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            i <= pre.len(),
            str.len() >= pre.len(),
            forall|j: int| 0 <= j < i ==> str[j] == pre[j]
    {
        if str[i] != pre[i] {
            // At this point, we know str[i] != pre[i], so the prefix doesn't match
            assert(!isPrefixPredicate(pre, str)) by {
                // The subrange won't equal pre because they differ at position i
                let sub = str.subrange(0, pre.len() as int);
                assert(sub[i as int] == str[i as int]);
                assert(pre[i as int] != str[i as int]);
                assert(sub != pre);
            };
            return false;
        }
        i += 1;
    }
    
    // At this point, we've verified all characters match
    assert(isPrefixPredicate(pre, str)) by {
        assert(str.len() >= pre.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> str[j] == pre[j]);
        let sub = str.subrange(0, pre.len() as int);
        assert(sub.len() == pre.len());
        // Prove equality by showing each element is equal
        assert(forall|k: int| 0 <= k < pre.len() ==> sub[k] == pre[k]) by {
            assert(forall|k: int| 0 <= k < pre.len() ==> sub[k] == str[k]);
            assert(forall|k: int| 0 <= k < pre.len() ==> str[k] == pre[k]);
        };
        // Use extensional equality
        assert(sub == pre);
    };
    
    return true;
}

}