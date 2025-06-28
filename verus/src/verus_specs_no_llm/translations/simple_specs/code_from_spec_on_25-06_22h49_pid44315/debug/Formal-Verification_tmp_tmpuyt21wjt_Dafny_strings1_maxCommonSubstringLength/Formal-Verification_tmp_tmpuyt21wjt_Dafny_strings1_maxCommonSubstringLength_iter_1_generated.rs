use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn maxCommonSubstringPredicate(str1: String, str2: String, len: nat) -> bool {
    len <= str1.len() && len <= str2.len() &&
    (len == 0 || haveCommonKSubstringPredicate(len, str1, str2)) &&
    (forall|k: nat| len < k && k <= str1.len() && k <= str2.len() ==> !haveCommonKSubstringPredicate(k, str1, str2))
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && 
    (exists|i: nat| i <= str.len() - sub.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && 
    (forall|i: nat| i < pre.len() ==> pre.spec_index(i..i+1) == str.spec_index(i..i+1))
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && 
    (exists|i: nat| i <= str1.len() - k && 
        isSubstringPredicate(str1.spec_index(i..i+k), str2))
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res == isSubstringPredicate(sub, str)
{
    if str.len() < sub.len() {
        return false;
    }
    
    let mut i = 0;
    while i <= str.len() - sub.len()
        invariant 
            i <= str.len() - sub.len() + 1,
            forall|j: nat| j < i ==> !isPrefixPredicate(sub, str.spec_index(j..))
    {
        if isPrefix(sub, str.spec_index(i..)) {
            return true;
        }
        i += 1;
    }
    false
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures pre.len() > str.len() ==> !res
    ensures res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i = 0;
    while i < pre.len()
        invariant 
            i <= pre.len(),
            forall|j: nat| j < i ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1)
    {
        if pre.spec_index(i..i+1) != str.spec_index(i..i+1) {
            return false;
        }
        i += 1;
    }
    true
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures str1.len() < k || str2.len() < k ==> !found
    ensures haveCommonKSubstringPredicate(k, str1, str2) == found
{
    if str1.len() < k || str2.len() < k {
        return false;
    }
    
    let mut i = 0;
    while i <= str1.len() - k
        invariant 
            i <= str1.len() - k + 1,
            forall|j: nat| j < i ==> !isSubstringPredicate(str1.spec_index(j..j+k), str2)
    {
        let substring = str1.spec_index(i..i+k);
        if isSubstring(substring, str2) {
            return true;
        }
        i += 1;
    }
    false
}

fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    ensures 
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len)
{
    let max_possible = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
    
    let mut k = max_possible;
    while k > 0
        invariant 
            k <= max_possible,
            forall|j: nat| k < j && j <= max_possible ==> !haveCommonKSubstringPredicate(j, str1, str2)
    {
        if haveCommonKSubstring(k, str1, str2) {
            return k;
        }
        k -= 1;
    }
    0
}

}