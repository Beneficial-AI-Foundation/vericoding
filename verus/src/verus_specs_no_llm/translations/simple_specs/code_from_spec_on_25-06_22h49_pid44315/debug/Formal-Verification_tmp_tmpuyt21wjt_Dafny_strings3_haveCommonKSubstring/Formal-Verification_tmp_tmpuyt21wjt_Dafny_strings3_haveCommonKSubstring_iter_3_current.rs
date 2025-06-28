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
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && isSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| (0 <= i1 && i1 + k <= str1.len()) ==> isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i + sub.len() <= str.len()
        invariant 
            0 <= i <= str.len(),
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
    {
        let suffix = str.subrange(i as int, str.len() as int);
        let is_prefix = isPrefix(sub.clone(), suffix);
        if is_prefix {
            assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
            assert(isSubstringPred(sub, str));
            return true;
        }
        assert(isNotPrefixPred(sub, str.subrange(i as int, str.len() as int)));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
    false
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
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            pre.subrange(0, i as int) == str.subrange(0, i as int)
    {
        if pre.get_char(i as int) != str.get_char(i as int) {
            assert(pre != str.subrange(0, pre.len() as int));
            return false;
        }
        i += 1;
    }
    
    assert(pre.subrange(0, pre.len() as int) == str.subrange(0, pre.len() as int));
    assert(pre == str.subrange(0, pre.len() as int));
    true
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i + k <= str1.len()
        invariant 
            0 <= i <= str1.len(),
            k <= str1.len(),
            k > 0,
            forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)
    {
        let substring = str1.subrange(i as int, i as int + k as int);
        let is_common = isSubstring(substring, str2.clone());
        if is_common {
            assert(isSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        assert(isNotSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + k <= str1.len()) ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2));
    false
}

}