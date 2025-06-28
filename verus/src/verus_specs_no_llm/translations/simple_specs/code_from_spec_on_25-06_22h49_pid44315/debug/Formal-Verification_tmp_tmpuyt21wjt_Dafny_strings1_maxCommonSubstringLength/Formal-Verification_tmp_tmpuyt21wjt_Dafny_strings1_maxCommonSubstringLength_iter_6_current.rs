use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn maxCommonSubstringPredicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool {
    len <= str1.len() && len <= str2.len() &&
    (len == 0 || haveCommonKSubstringPredicate(len, str1, str2)) &&
    (forall|k: nat| len < k && k <= str1.len() && k <= str2.len() ==> !haveCommonKSubstringPredicate(k, str1, str2))
}

spec fn isSubstringPredicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && 
    (exists|i: nat| i <= str.len() - sub.len() && isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)))
}

spec fn isPrefixPredicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && 
    (forall|i: nat| i < pre.len() ==> pre[i as int] == str[i as int])
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && 
    (exists|i: nat| i <= str1.len() - k && 
        isSubstringPredicate(str1.subrange(i as int, (i + k) as int), str2))
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == isSubstringPredicate(sub, str)
{
    if str.len() < sub.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant 
            i <= str.len() - sub.len() + 1,
            forall|j: nat| j < i ==> !isPrefixPredicate(sub, str.subrange(j as int, str.len() as int)),
            str.len() >= sub.len()
        decreases str.len() - sub.len() + 1 - i
    {
        if isPrefix(sub, str.subrange(i as int, str.len() as int)) {
            assert(i <= str.len() - sub.len());
            assert(isPrefixPredicate(sub, str.subrange(i as int, str.len() as int)));
            return true;
        }
        i += 1;
    }
    assert(forall|j: nat| j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.subrange(j as int, str.len() as int)));
    false
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures pre.len() > str.len() ==> !res
    ensures res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            i <= pre.len(),
            forall|j: nat| j < i ==> pre[j as int] == str[j as int],
            str.len() >= pre.len()
        decreases pre.len() - i
    {
        if pre[i as int] != str[i as int] {
            assert(exists|k: nat| k < pre.len() && pre[k as int] != str[k as int]);
            return false;
        }
        i += 1;
    }
    assert(forall|j: nat| j < pre.len() ==> pre[j as int] == str[j as int]);
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures str1.len() < k || str2.len() < k ==> !found
    ensures haveCommonKSubstringPredicate(k, str1, str2) == found
{
    if str1.len() < k || str2.len() < k {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str1.len() - k
        invariant 
            i <= str1.len() - k + 1,
            forall|j: nat| j < i ==> !isSubstringPredicate(str1.subrange(j as int, (j + k) as int), str2),
            str1.len() >= k,
            str2.len() >= k
        decreases str1.len() - k + 1 - i
    {
        let substring = str1.subrange(i as int, (i + k) as int);
        if isSubstring(substring, str2) {
            assert(i <= str1.len() - k);
            assert(isSubstringPredicate(str1.subrange(i as int, (i + k) as int), str2));
            return true;
        }
        i += 1;
    }
    assert(forall|j: nat| j <= str1.len() - k ==> !isSubstringPredicate(str1.subrange(j as int, (j + k) as int), str2));
    false
}

fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    ensures 
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len)
{
    let max_possible = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
    
    let mut k: usize = max_possible;
    while k > 0
        invariant 
            k <= max_possible,
            forall|j: nat| k < j && j <= max_possible ==> !haveCommonKSubstringPredicate(j, str1, str2),
            forall|j: nat| k < j && j <= str1.len() && j <= str2.len() ==> !haveCommonKSubstringPredicate(j, str1, str2),
            max_possible <= str1.len() && max_possible <= str2.len()
        decreases k
    {
        if haveCommonKSubstring(k as nat, str1, str2) {
            assert(haveCommonKSubstringPredicate(k as nat, str1, str2));
            assert(k <= max_possible);
            assert(k <= str1.len() && k <= str2.len());
            assert(forall|j: nat| k < j && j <= str1.len() && j <= str2.len() ==> !haveCommonKSubstringPredicate(j, str1, str2));
            return k as nat;
        }
        k -= 1;
    }
    
    // At this point k == 0
    assert(forall|j: nat| 0 < j && j <= str1.len() && j <= str2.len() ==> !haveCommonKSubstringPredicate(j, str1, str2));
    assert(0 <= str1.len() && 0 <= str2.len());
    0
}

}