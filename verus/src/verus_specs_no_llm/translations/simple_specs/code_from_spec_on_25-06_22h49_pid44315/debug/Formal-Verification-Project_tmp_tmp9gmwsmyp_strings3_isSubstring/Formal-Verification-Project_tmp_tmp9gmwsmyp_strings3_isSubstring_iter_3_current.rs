use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len() as int)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.spec_index(i..))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len() as int)
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..))
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        proof {
            assert(isNotPrefixPred(pre, str));
        }
        false
    } else {
        let prefix_slice = str.substring(0, pre.len());
        let result = pre == prefix_slice;
        proof {
            assert(prefix_slice == str.spec_index(..pre.len() as int));
            if result {
                assert(isPrefixPred(pre, str));
            } else {
                assert(isNotPrefixPred(pre, str));
            }
        }
        result
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        proof {
            assert(forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..))) by {
                assert(forall|i: int| 0 <= i <= str.len() ==> str.spec_index(i..).len() < sub.len());
            };
            assert(isNotSubstringPred(sub, str));
        }
        return false;
    }
    
    if sub.len() == 0 {
        proof {
            assert(isPrefixPred(sub, str.spec_index(0..)));
            assert(isSubstringPred(sub, str));
        }
        return true;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 0 <= i <= str.len() - sub.len() + 1
        invariant sub.len() > 0
        invariant sub.len() <= str.len()
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        let substr = str.substring(i, str.len());
        if isPrefix(sub.clone(), substr.clone()) {
            proof {
                assert(substr == str.spec_index(i as int..));
                assert(isPrefixPred(sub, str.spec_index(i as int..)));
                assert(isSubstringPred(sub, str));
            }
            return true;
        }
        proof {
            assert(substr == str.spec_index(i as int..));
            assert(isNotPrefixPred(sub, str.spec_index(i as int..)));
        }
        i += 1;
    }
    
    proof {
        assert(i == str.len() - sub.len() + 1);
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> isNotPrefixPred(sub, str.spec_index(j..)));
        assert(forall|j: int| str.len() - sub.len() < j <= str.len() ==> isNotPrefixPred(sub, str.spec_index(j..))) by {
            assert(forall|j: int| str.len() - sub.len() < j <= str.len() ==> 
                str.spec_index(j..).len() < sub.len());
        };
        assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.spec_index(j..)));
        assert(isNotSubstringPred(sub, str));
    }
    false
}

}