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
            forall|j: int| 0 <= j < i ==> #[trigger] str[j] == pre[j]
    {
        if str[i] != pre[i] {
            // At this point, we know str[i] != pre[i], so the prefix doesn't match
            assert(!isPrefixPredicate(pre, str)) by {
                let sub = str.subrange(0, pre.len() as int);
                assert(sub[i as int] == str[i as int]);
                assert(str[i as int] != pre[i as int]);
                assert(sub[i as int] != pre[i as int]);
                assert(sub != pre);
            };
            return false;
        }
        i += 1;
    }
    
    // At this point, we've verified all characters match
    assert(isPrefixPredicate(pre, str)) by {
        assert(str.len() >= pre.len());
        let sub = str.subrange(0, pre.len() as int);
        assert(sub.len() == pre.len());
        
        // From loop invariant, we know all characters match
        assert(forall|k: int| 0 <= k < pre.len() ==> #[trigger] str[k] == pre[k]);
        
        // Prove that subrange elements equal pre elements
        assert(forall|k: int| 0 <= k < pre.len() ==> #[trigger] sub[k] == str[k]);
        assert(forall|k: int| 0 <= k < pre.len() ==> #[trigger] sub[k] == pre[k]);
        
        // Use sequence extensionality to prove equality
        assert(sub == pre) by {
            assert(sub.len() == pre.len());
            assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == pre[k]);
        };
    };
    
    return true;
}

}