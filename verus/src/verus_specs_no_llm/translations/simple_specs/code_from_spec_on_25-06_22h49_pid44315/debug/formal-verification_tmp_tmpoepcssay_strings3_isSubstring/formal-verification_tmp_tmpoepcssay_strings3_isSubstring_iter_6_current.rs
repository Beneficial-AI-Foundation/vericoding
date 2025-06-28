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
    ensures 
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        assert(isNotPrefixPred(pre, str));
        false
    } else {
        // Convert to bytes for comparison
        let pre_bytes = pre.as_bytes();
        let str_bytes = str.as_bytes();
        
        let mut i = 0;
        while i < pre.len()
            invariant
                0 <= i <= pre.len(),
                pre.len() <= str.len(),
                pre_bytes == pre.as_bytes(),
                str_bytes == str.as_bytes(),
                forall|j: int| 0 <= j < i ==> pre_bytes[j] == str_bytes[j]
        {
            if pre_bytes[i] != str_bytes[i] {
                // Found a mismatch
                assert(exists|k: int| 0 <= k < pre.len() && pre_bytes[k] != str_bytes[k]);
                assert(pre != str.spec_index(..pre.len() as int)) by {
                    // The byte difference implies string difference
                    assert(pre.as_bytes()[i as int] != str.as_bytes()[i as int]);
                };
                assert(isNotPrefixPred(pre, str));
                return false;
            }
            i += 1;
        }
        
        // All bytes matched
        assert(forall|j: int| 0 <= j < pre.len() ==> pre_bytes[j] == str_bytes[j]);
        
        // Prove string equality
        assert(pre == str.spec_index(..pre.len() as int)) by {
            assert(pre.len() == (str.spec_index(..pre.len() as int)).len());
            assert(forall|j: int| 0 <= j < pre.len() ==> pre.as_bytes()[j] == str.as_bytes()[j]);
        };
        
        assert(isPrefixPred(pre, str));
        true
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        // Sub is longer than str, so it can't be a substring
        assert(forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..))) by {
            assert forall|i: int| 0 <= i <= str.len() implies isNotPrefixPred(sub, str.spec_index(i..)) by {
                let remaining = str.spec_index(i..);
                assert(remaining.len() == str.len() - i);
                assert(sub.len() > str.len() >= remaining.len());
                assert(isNotPrefixPred(sub, remaining));
            }
        };
        assert(isNotSubstringPred(sub, str));
        return false;
    }
    
    let mut i = 0;
    let bound = str.len() - sub.len() + 1;
    while i < bound
        invariant 
            0 <= i <= bound,
            bound == str.len() - sub.len() + 1,
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
        decreases bound - i
    {
        let remaining_str = str.spec_index(i as int..);
        
        if isPrefix(sub, remaining_str) {
            // Found a match at position i
            assert(isPrefixPred(sub, remaining_str));
            assert(isPrefixPred(sub, str.spec_index(i as int..)));
            assert(exists|k: int| 0 <= k <= str.len() && isPrefixPred(sub, str.spec_index(k..))) by {
                assert(0 <= i <= str.len() && isPrefixPred(sub, str.spec_index(i as int..)));
            };
            assert(isSubstringPred(sub, str));
            return true;
        }
        
        // No match at position i
        assert(!isPrefixPred(sub, remaining_str));
        assert(isNotPrefixPred(sub, remaining_str));
        assert(isNotPrefixPred(sub, str.spec_index(i as int..)));
        
        i += 1;
    }
    
    // Checked all valid positions and found no match
    assert(i == bound);
    assert(forall|j: int| 0 <= j < bound ==> isNotPrefixPred(sub, str.spec_index(j..)));
    assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> isNotPrefixPred(sub, str.spec_index(j..)));
    
    // For positions beyond str.len() - sub.len(), remaining string is too short
    assert forall|j: int| str.len() - sub.len() < j <= str.len() implies isNotPrefixPred(sub, str.spec_index(j..)) by {
        let remaining = str.spec_index(j..);
        assert(remaining.len() == str.len() - j);
        assert(remaining.len() < sub.len());
        assert(isNotPrefixPred(sub, remaining));
    };
    
    // Combine both cases
    assert(forall|j: int| 0 <= j <= str.len() ==> isNotPrefixPred(sub, str.spec_index(j..)));
    assert(isNotSubstringPred(sub, str));
    false
}

}