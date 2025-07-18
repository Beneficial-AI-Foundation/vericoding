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

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 0 <= i <= pre.len()
        invariant pre.len() <= str.len()
        invariant pre.spec_index(..i as int) == str.spec_index(..i as int)
    {
        if pre.spec_index(i as int..i as int + 1) != str.spec_index(i as int..i as int + 1) {
            assert(pre != str.spec_index(..pre.len() as int));
            return false;
        }
        i = i + 1;
    }
    assert(pre.spec_index(..pre.len() as int) == str.spec_index(..pre.len() as int));
    true
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures res ==> isSubstringPred(sub, str)
    ensures isSubstringPred(sub, str) ==> res
    ensures !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 0 <= i <= str.len() - sub.len() + 1
        invariant sub.len() <= str.len()
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        if isPrefix(sub, str.spec_index(i as int..)) {
            assert(isPrefixPred(sub, str.spec_index(i as int..)));
            return true;
        }
        assert(isNotPrefixPred(sub, str.spec_index(i as int..)));
        i = i + 1;
    }
    false
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k as usize > str1.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str1.len() - k as usize
        invariant 0 <= i <= str1.len() - k + 1
        invariant k <= str1.len()
        invariant forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.spec_index(j..j+k as int), str2)
    {
        let substring = str1.spec_index(i as int..i as int + k as int);
        if isSubstring(substring, str2) {
            assert(isSubstringPred(substring, str2));
            return true;
        }
        assert(isNotSubstringPred(substring, str2));
        i = i + 1;
    }
    false
}

fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures forall|k: nat| len < k <= str1.len() ==> !haveCommonKSubstringPred(k, str1, str2)
    ensures len == 0 || haveCommonKSubstringPred(len, str1, str2)
{
    if str1.len() == 0 {
        return 0;
    }
    
    let mut k: usize = str1.len();
    
    while k > 0
        invariant 0 <= k <= str1.len()
        invariant forall|j: nat| k < j <= str1.len() ==> !haveCommonKSubstringPred(j, str1, str2)
    {
        if haveCommonKSubstring(k as nat, str1, str2) {
            assert(haveCommonKSubstringPred(k as nat, str1, str2));
            return k as nat;
        }
        assert(!haveCommonKSubstringPred(k as nat, str1, str2));
        k = k - 1;
    }
    0
}

}