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
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 0 <= i <= pre.len()
        invariant pre.spec_index(..i as int) == str.spec_index(..i as int)
    {
        if pre.spec_index(i as int..(i+1) as int) != str.spec_index(i as int..(i+1) as int) {
            return false;
        }
        i += 1;
    }
    true
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        return false;
    }
    
    let limit = str.len() - sub.len();
    let mut i: usize = 0;
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant limit == str.len() - sub.len()
        invariant sub.len() <= str.len()
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        let prefix_check = isPrefix(sub, str.spec_index(i as int..));
        if prefix_check {
            assert(isPrefixPred(sub, str.spec_index(i as int..)));
            assert(isSubstringPred(sub, str));
            return true;
        } else {
            assert(isNotPrefixPred(sub, str.spec_index(i as int..)));
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> isNotPrefixPred(sub, str.spec_index(j..)));
    assert(isNotSubstringPred(sub, str));
    false
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        return false;
    }
    
    let limit = str1.len() - k;
    let mut i: usize = 0;
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant limit == str1.len() - k
        invariant k <= str1.len()
        invariant forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.spec_index(j..j+k as int), str2)
    {
        let substring = str1.spec_index(i as int..(i + k) as int);
        if isSubstring(substring, str2) {
            assert(isSubstringPred(substring, str2));
            assert(exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.spec_index(i1..j1), str2));
            return true;
        } else {
            assert(isNotSubstringPred(substring, str2));
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j <= str1.len() - k ==> isNotSubstringPred(str1.spec_index(j..j+k as int), str2));
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    false
}

fn maxCommonSubstringLength(str1: String, str2: String) -> (len: nat)
    requires str1.len() <= str2.len()
    ensures forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPred(k as nat, str1, str2)
    ensures len == 0 || haveCommonKSubstringPred(len, str1, str2)
{
    let mut max_len: nat = 0;
    let mut k: usize = 0;
    
    while k <= str1.len()
        invariant 0 <= k <= str1.len() + 1
        invariant max_len < k
        invariant max_len <= str1.len()
        invariant max_len == 0 || haveCommonKSubstringPred(max_len, str1, str2)
        invariant forall|j: int| max_len < j < k ==> !haveCommonKSubstringPred(j as nat, str1, str2)
    {
        if haveCommonKSubstring(k as nat, str1, str2) {
            max_len = k as nat;
        }
        k += 1;
    }
    
    max_len
}

}