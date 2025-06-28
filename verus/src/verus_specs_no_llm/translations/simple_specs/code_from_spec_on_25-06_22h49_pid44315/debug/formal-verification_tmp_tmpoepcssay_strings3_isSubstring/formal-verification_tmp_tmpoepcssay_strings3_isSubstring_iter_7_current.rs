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
        false
    } else {
        let mut i = 0;
        while i < pre.len()
            invariant
                0 <= i <= pre.len(),
                pre.len() <= str.len(),
                forall|j: int| 0 <= j < i ==> pre.as_bytes()[j] == str.as_bytes()[j]
        {
            if pre.as_bytes()[i] != str.as_bytes()[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
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
            return true;
        }
        
        i += 1;
    }
    
    false
}

}