use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        let prefix_part = str.subrange(0, pre.len() as int);
        pre == prefix_part
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    let mut i: usize = 0;
    
    while i <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
        decreases str.len() + 1 - i
    {
        if i as int <= str.len() {
            if isPrefix(sub, str.subrange(i as int, str.len() as int)) {
                // Prove that we found a valid substring position
                assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
                assert(0 <= i as int <= str.len());
                assert(isSubstringPred(sub, str)) by {
                    assert(exists|j: int| 0 <= j <= str.len() && isPrefixPred(sub, str.subrange(j, str.len() as int))) by {
                        assert(0 <= i as int <= str.len() && isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
                    }
                }
                return true;
            }
            
            // Record that position i doesn't work
            assert(isNotPrefixPred(sub, str.subrange(i as int, str.len() as int)));
        }
        
        i = i + 1;
    }
    
    // At this point, i > str.len(), so we've checked all valid positions
    assert(i > str.len());
    assert(forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
    
    // Since i > str.len(), we have checked all positions 0..=str.len()
    assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))) by {
        assert(forall|j: int| 0 <= j <= str.len() ==> j < i);
    }
    assert(isNotSubstringPred(sub, str));
    false
}

}