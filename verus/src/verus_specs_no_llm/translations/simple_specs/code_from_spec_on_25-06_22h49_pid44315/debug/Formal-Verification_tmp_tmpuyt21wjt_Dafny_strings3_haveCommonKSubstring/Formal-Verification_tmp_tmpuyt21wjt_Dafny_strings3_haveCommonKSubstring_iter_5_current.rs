use builtin::*;
use builtin_macros::*;

verus! {

type nat = usize;

fn main() {
}

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && isSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int| (0 <= i1 && i1 + k <= str1.len()) ==> isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        assert(forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))) by {
            // Empty range - vacuously true
        }
        return false;
    }
    
    let mut i: usize = 0;
    while i + sub.len() <= str.len()
        invariant 
            0 <= i <= str.len(),
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))
        decreases str.len() - i
    {
        let suffix = str.subrange(i as int, str.len() as int);
        let is_prefix = isPrefix(sub, suffix);
        if is_prefix {
            assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
            assert(isSubstringPred(sub, str)) by {
                assert(0 <= i && i + sub.len() <= str.len());
                assert(isPrefixPred(sub, str.subrange(i as int, str.len() as int)));
            }
            return true;
        }
        assert(isNotPrefixPred(sub, str.subrange(i as int, str.len() as int)));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int))) by {
        assert(forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
        assert(i + sub.len() > str.len());
    }
    assert(isNotSubstringPred(sub, str));
    false
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre, str)
    ensures res <==> isPrefixPred(pre, str)
{
    if pre.len() > str.len() {
        assert(isNotPrefixPred(pre, str));
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|k: int| 0 <= k < i ==> pre[k] == str[k]
        decreases pre.len() - i
    {
        if pre[i as int] != str[i as int] {
            assert(pre != str.subrange(0, pre.len() as int)) by {
                assert(pre[i as int] != str[i as int]);
                assert(forall|k: int| 0 <= k < i ==> pre[k] == str[k]);
            }
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    assert(pre == str.subrange(0, pre.len() as int)) by {
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str[k]);
        assert(pre.len() == str.subrange(0, pre.len() as int).len());
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str.subrange(0, pre.len() as int)[k]);
    }
    assert(isPrefixPred(pre, str));
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        assert(forall|j: int| (0 <= j && j + k <= str1.len()) ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)) by {
            // Empty range - vacuously true
        }
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        return false;
    }
    
    let mut i: usize = 0;
    while i + k <= str1.len()
        invariant 
            0 <= i <= str1.len(),
            k <= str1.len(),
            k > 0,
            forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)
        decreases str1.len() - i
    {
        let substring = str1.subrange(i as int, i as int + k as int);
        let is_common = isSubstring(substring, str2);
        if is_common {
            assert(isSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
            assert(haveCommonKSubstringPred(k, str1, str2)) by {
                assert(0 <= i && i + k <= str1.len());
                assert(isSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
            }
            return true;
        }
        assert(isNotSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + k <= str1.len()) ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)) by {
        assert(forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2));
        assert(i + k > str1.len());
    }
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    false
}

}