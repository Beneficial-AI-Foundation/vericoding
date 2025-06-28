use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(..pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.spec_index(i1..j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.spec_index(i1..j1), str2)
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

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    let mut i = 0;
    while i <= str.len() 
        invariant 0 <= i <= str.len() + 1
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        if i + sub.len() <= str.len() {
            let prefix_check = isPrefix(sub, str.spec_index(i..));
            if prefix_check {
                return true;
            }
        }
        i += 1;
    }
    false
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i = 0;
    while i < pre.len()
        invariant 0 <= i <= pre.len()
        invariant pre.spec_index(..i as int) == str.spec_index(..i as int)
    {
        if pre.spec_index(i..i+1) != str.spec_index(i..i+1) {
            return false;
        }
        i += 1;
    }
    true
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        return false;
    }
    
    let mut i = 0;
    while i <= str1.len() - k
        invariant 0 <= i <= str1.len() - k + 1
        invariant forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.spec_index(j..j+k as int), str2)
    {
        let substring = str1.spec_index(i..i + k as int);
        if isSubstring(substring, str2) {
            return true;
        }
        i += 1;
    }
    false
}

fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPred(k as nat, str1, str2)
    ensures len <= str1.len() ==> haveCommonKSubstringPred(len, str1, str2)
{
    let mut max_len = 0;
    let mut k = 0;
    
    while k <= str1.len()
        invariant 0 <= k <= str1.len() + 1
        invariant max_len <= k
        invariant max_len <= str1.len()
        invariant max_len > 0 ==> haveCommonKSubstringPred(max_len, str1, str2)
        invariant forall|j: int| max_len < j < k ==> !haveCommonKSubstringPred(j as nat, str1, str2)
    {
        if haveCommonKSubstring(k, str1, str2) {
            max_len = k;
        }
        k += 1;
    }
    
    max_len
}

}