use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.spec_index(0..pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
        isSubstringPred(str1.spec_index(i1..i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k <= str1.len() ==> 
        isNotSubstringPred(str1.spec_index(i1..i1 + k as int), str2)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i && i <= str.len() && isPrefixPred(sub, str.spec_index(i..str.len()))
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| 0 <= i && i <= str.len() ==> isNotPrefixPred(sub, str.spec_index(i..str.len()))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(0..pre.len() as int)
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    let mut i = 0;
    while i <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..str.len()))
    {
        if i + sub.len() <= str.len() {
            if isPrefix(sub.clone(), str.spec_index(i..str.len())) {
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
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1)
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
    while i + k <= str1.len()
        invariant 
            0 <= i <= str1.len() + 1,
            forall|j: int| 0 <= j < i && j + k <= str1.len() ==> 
                isNotSubstringPred(str1.spec_index(j..j + k as int), str2)
    {
        let substring = str1.spec_index(i..i + k as int);
        if isSubstring(substring, str2.clone()) {
            return true;
        }
        i += 1;
    }
    false
}

fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures 
        (forall|k: nat| len < k && k <= str1.len() ==> !haveCommonKSubstringPred(k, str1, str2)),
        len <= str1.len() ==> haveCommonKSubstringPred(len, str1, str2)
{
    let mut maxLen = 0;
    let mut k = 1;
    
    while k <= str1.len()
        invariant 
            0 <= maxLen < k <= str1.len() + 1,
            forall|j: nat| maxLen < j < k ==> !haveCommonKSubstringPred(j, str1, str2),
            maxLen == 0 || haveCommonKSubstringPred(maxLen, str1, str2)
    {
        if haveCommonKSubstring(k, str1.clone(), str2.clone()) {
            maxLen = k;
        }
        k += 1;
    }
    
    maxLen
}

}