use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k as int <= str1.len() && 
        isSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k as int <= str1.len() ==> 
        isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i && i + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    let mut i: int = 0;
    while i + sub.len() <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i && j + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len()))
        decreases str.len() - i
    {
        if isPrefix(sub, str.subrange(i, str.len())) {
            return true;
        }
        i += 1;
    }
    
    false
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: int = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        decreases pre.len() - i
    {
        if pre[i] != str[i] {
            return false;
        }
        i += 1;
    }
    
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k as int > str1.len() {
        return false;
    }
    
    let mut i: int = 0;
    while i + k as int <= str1.len()
        invariant 
            0 <= i <= str1.len() + 1,
            forall|j: int| 0 <= j < i && j + k as int <= str1.len() ==> 
                isNotSubstringPred(str1.subrange(j, j + k as int), str2)
        decreases str1.len() - i
    {
        let substring = str1.subrange(i, i + k as int);
        if isSubstring(substring, str2) {
            return true;
        }
        i += 1;
    }
    
    false
}

fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures 
        (forall|k: nat| len < k && k <= str1.len() ==> !haveCommonKSubstringPred(k, str1, str2)),
        len == 0 || haveCommonKSubstringPred(len, str1, str2)
{
    let mut maxLen: nat = 0;
    let mut k: nat = 1;
    
    while k as int <= str1.len()
        invariant 
            0 <= maxLen,
            maxLen < k,
            k <= str1.len() + 1,
            forall|j: nat| maxLen < j < k ==> !haveCommonKSubstringPred(j, str1, str2),
            maxLen == 0 || haveCommonKSubstringPred(maxLen, str1, str2)
        decreases str1.len() - k as int + 1
    {
        if haveCommonKSubstring(k, str1, str2) {
            maxLen = k;
        }
        k += 1;
    }
    
    maxLen
}

}