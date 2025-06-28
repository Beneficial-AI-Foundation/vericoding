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
    exists|i: int| 0 <= i <= sub.len() + (str.len() - sub.len()) && i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
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
        proof {
            assert(isNotPrefixPred(pre, str));
        }
        false
    } else {
        let prefix_slice = str.subrange(0, pre.len() as int);
        let result = pre == prefix_slice;
        proof {
            if result {
                assert(isPrefixPred(pre, str));
            } else {
                assert(isNotPrefixPred(pre, str));
            }
        }
        result
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        proof {
            assert(forall|i: int| 0 <= i <= str.len() ==> {
                let substr = str.subrange(i, str.len() as int);
                substr.len() == str.len() - i && str.len() - i <= str.len() < sub.len()
            });
            assert(forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int)));
            assert(isNotSubstringPred(sub, str));
        }
        return false;
    }
    
    if sub.len() == 0 {
        proof {
            assert(isPrefixPred(sub, str.subrange(0, str.len() as int)));
            assert(isSubstringPred(sub, str));
        }
        return true;
    }
    
    // Now we know sub.len() > 0 and sub.len() <= str.len()
    let mut i: usize = 0;
    let end_pos = str.len() - sub.len();  // This is safe since sub.len() <= str.len()
    let limit = end_pos as usize;
    
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant limit as int == str.len() - sub.len()
        invariant end_pos == str.len() - sub.len()
        invariant sub.len() > 0
        invariant sub.len() <= str.len()
        invariant str.len() >= sub.len()
        invariant end_pos >= 0
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
    {
        let substr = str.subrange(i as int, str.len() as int);
        if isPrefix(sub, substr) {
            proof {
                assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
                assert(isSubstringPred(sub, str));
            }
            return true;
        }
        proof {
            assert(isNotPrefixPred(sub, str.subrange(i as int, str.len() as int)));
        }
        i += 1;
    }
    
    proof {
        assert(i == limit + 1);
        assert(limit as int == str.len() - sub.len());
        assert(end_pos == str.len() - sub.len());
        
        // We've checked all positions from 0 to end_pos (inclusive)
        assert(forall|j: int| 0 <= j <= end_pos ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
        
        // For positions beyond end_pos, the remaining substring is too short
        assert(forall|j: int| end_pos < j <= str.len() ==> {
            let substr = str.subrange(j, str.len() as int);
            substr.len() == str.len() - j < sub.len()
        });
        assert(forall|j: int| end_pos < j <= str.len() ==> 
            isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
        
        // Combine both ranges
        assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))) by {
            assert(forall|j: int| 0 <= j <= str.len() ==> {
                (0 <= j <= end_pos) || (end_pos < j <= str.len())
            });
        };
        assert(isNotSubstringPred(sub, str));
    }
    false
}

}