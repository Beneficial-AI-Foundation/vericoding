use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && 
    (exists|i: int| 0 <= i <= str1.len() - k && 
        isSubstringPredicate(str1.spec_index(i..i+k), str2))
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures 
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        // Check if pre is a prefix of str
        let mut i = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j)
        {
            if pre.spec_index(i) != str.spec_index(i) {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res == isSubstringPredicate(sub, str)
{
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i = 0;
    while i <= str.len() - sub.len()
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.spec_index(j..))
    {
        if isPrefix(sub, str.spec_index(i..)) {
            return true;
        }
        i += 1;
    }
    false
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures
        str1.len() < k || str2.len() < k ==> !found,
        found == haveCommonKSubstringPredicate(k, str1, str2)
{
    if str1.len() < k || str2.len() < k {
        return false;
    }
    
    let mut i = 0;
    while i <= str1.len() - k
        invariant 
            0 <= i <= str1.len() - k + 1,
            forall|j: int| 0 <= j < i ==> !isSubstringPredicate(str1.spec_index(j..j+k), str2)
    {
        let substring = str1.spec_index(i..i+k);
        if isSubstring(substring, str2) {
            return true;
        }
        i += 1;
    }
    false
}

}