use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && 
    (forall|i: int| 0 <= i < pre.len() ==> pre[i] == str[i])
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && 
    (exists|i: int| 0 <= i <= str.len() - sub.len() && 
        isPrefixPredicate(sub, str.subrange(i, i + sub.len())))
}

spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && 
    (exists|i: int| 0 <= i <= str1.len() - k && 
        isSubstringPredicate(str1.subrange(i, i + k), str2))
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures 
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str)
{
    if pre.len() > str.len() {
        false
    } else {
        let mut i = 0;
        while i < pre.len()
            invariant 
                0 <= i <= pre.len(),
                pre.len() <= str.len(),
                forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        {
            if pre[i] != str[i] {
                assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j] ==> j < i);
                return false;
            }
            i += 1;
        }
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]);
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
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> !isPrefixPredicate(sub, str.subrange(j, j + sub.len()))
        decreases str.len() - sub.len() + 1 - i
    {
        if isPrefix(sub, str.subrange(i, i + sub.len())) {
            assert(isPrefixPredicate(sub, str.subrange(i, i + sub.len())));
            assert(0 <= i <= str.len() - sub.len());
            return true;
        }
        assert(!isPrefixPredicate(sub, str.subrange(i, i + sub.len())));
        i += 1;
    }
    assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isPrefixPredicate(sub, str.subrange(j, j + sub.len())));
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
            str1.len() >= k,
            str2.len() >= k,
            forall|j: int| 0 <= j < i ==> !isSubstringPredicate(str1.subrange(j, j + k), str2)
        decreases str1.len() - k + 1 - i
    {
        let substring = str1.subrange(i, i + k);
        if isSubstring(substring, str2) {
            assert(isSubstringPredicate(substring, str2));
            assert(0 <= i <= str1.len() - k);
            return true;
        }
        assert(!isSubstringPredicate(str1.subrange(i, i + k), str2));
        i += 1;
    }
    assert(forall|j: int| 0 <= j <= str1.len() - k ==> !isSubstringPredicate(str1.subrange(j, j + k), str2));
    false
}

}