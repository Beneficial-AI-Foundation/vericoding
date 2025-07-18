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
            assert(forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))) by {
                assert(forall|i: int| 0 <= i <= str.len() ==> str.subrange(i, str.len() as int).len() <= str.len() - i);
                assert(forall|i: int| 0 <= i <= str.len() ==> str.len() - i < sub.len());
            }
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
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 0 <= i <= str.len() - sub.len() + 1
        invariant sub.len() > 0
        invariant sub.len() <= str.len()
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
        assert(i == str.len() - sub.len() + 1);
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
        assert(forall|j: int| str.len() - sub.len() < j <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))) by {
            assert(forall|j: int| str.len() - sub.len() < j <= str.len() ==> 
                str.subrange(j, str.len() as int).len() < sub.len());
        }
        assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
        assert(isNotSubstringPred(sub, str));
    }
    false
}

}