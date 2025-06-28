use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len())
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int| 0 <= i1 <= str1.len() - k && isSubstringPred(str1.spec_index(i1..i1 + k), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| 0 <= i1 <= str1.len() - k ==> isNotSubstringPred(str1.spec_index(i1..i1 + k), str2)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.spec_index(i..))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len())
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..))
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    let mut i = 0;
    while i <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        if i + sub.len() <= str.len() {
            let is_prefix = isPrefix(sub.clone(), str.spec_index(i..));
            if is_prefix {
                return true;
            }
        }
        i += 1;
    }
    false
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            pre.spec_index(..i) == str.spec_index(..i)
    {
        if pre.spec_index(i..i+1) != str.spec_index(i..i+1) {
            return false;
        }
        i += 1;
    }
    true
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        return false;
    }
    
    let mut i = 0;
    while i <= str1.len() - k
        invariant 
            0 <= i <= str1.len() - k + 1,
            forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.spec_index(j..j + k), str2)
    {
        let substring = str1.spec_index(i..i + k);
        let is_common = isSubstring(substring, str2.clone());
        if is_common {
            return true;
        }
        i += 1;
    }
    false
}

}