use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k as int <= str1.len() && isSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| 0 <= i1 && i1 + k as int <= str1.len() ==> isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| 0 <= i && i + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures res <==> isPrefixPred(pre, str)
    ensures !res <==> isNotPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        assert(isNotPrefixPred(pre, str));
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 0 <= i <= pre.len()
        invariant pre.len() <= str.len()
        invariant pre.subrange(0, i as int) == str.subrange(0, i as int)
    {
        if pre[i as int] != str[i as int] {
            assert(pre != str.subrange(0, pre.len() as int));
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    assert(pre == str.subrange(0, pre.len() as int));
    assert(isPrefixPred(pre, str));
    true
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        assert(forall|i: int| 0 <= i && i + sub.len() <= str.len() ==> false);
        assert(isNotSubstringPred(sub, str));
        return false;
    }
    
    if sub.len() == 0 {
        assert(isPrefixPred(sub, str.subrange(0, str.len())));
        assert(isSubstringPred(sub, str));
        return true;
    }
    
    let limit = str.len() - sub.len();
    let mut i: usize = 0;
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant limit == str.len() - sub.len()
        invariant sub.len() <= str.len()
        invariant sub.len() > 0
        invariant forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len()))
    {
        assert(i as int + sub.len() <= str.len());
        let prefix_check = isPrefix(sub, str.subrange(i as int, str.len()));
        if prefix_check {
            assert(isPrefixPred(sub, str.subrange(i as int, str.len())));
            assert(isSubstringPred(sub, str));
            return true;
        }
        assert(isNotPrefixPred(sub, str.subrange(i as int, str.len())));
        i += 1;
    }
    
    assert(i == limit + 1);
    assert(forall|j: int| 0 <= j && j + sub.len() <= str.len() ==> 0 <= j <= limit);
    assert(forall|j: int| 0 <= j && j + sub.len() <= str.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len())));
    assert(isNotSubstringPred(sub, str));
    false
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        assert(forall|i: int| 0 <= i && i + k as int <= str1.len() ==> false);
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        return false;
    }
    
    if k == 0 {
        let empty_string = str1.subrange(0, 0);
        assert(isSubstringPred(empty_string, str2));
        assert(haveCommonKSubstringPred(k, str1, str2));
        return true;
    }
    
    let limit = str1.len() - k;
    let mut i: usize = 0;
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant limit == str1.len() - k
        invariant k <= str1.len()
        invariant k > 0
        invariant forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)
    {
        assert(i as int + k as int <= str1.len());
        let substring = str1.subrange(i as int, (i as int) + (k as int));
        if isSubstring(substring, str2) {
            assert(isSubstringPred(substring, str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        assert(isNotSubstringPred(substring, str2));
        i += 1;
    }
    
    assert(i == limit + 1);
    assert(forall|j: int| 0 <= j && j + k as int <= str1.len() ==> 0 <= j <= limit);
    assert(forall|j: int| 0 <= j && j + k as int <= str1.len() ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2));
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
    
    assert(k == str1.len() + 1);
    assert(forall|j: int| max_len < j < k ==> !haveCommonKSubstringPred(j as nat, str1, str2));
    assert(forall|j: int| max_len < j <= str1.len() ==> !haveCommonKSubstringPred(j as nat, str1, str2));
    
    max_len
}

}