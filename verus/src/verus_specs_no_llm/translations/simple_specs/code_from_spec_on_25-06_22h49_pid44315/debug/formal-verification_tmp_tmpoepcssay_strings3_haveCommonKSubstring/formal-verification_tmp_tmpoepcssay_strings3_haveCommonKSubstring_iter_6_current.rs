use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
    pre@ == str@.subrange(0, pre.len() as int)
}

spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int| 0 <= i1 && i1 + k <= str1.len() && 
    isSubstringPred(str1@.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int| (0 <= i1 && i1 + k <= str1.len()) ==> 
    isNotSubstringPred(str1@.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: Seq<char>, str: String) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && 
    sub == str@.subrange(i, i + sub.len())
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre@ != str@.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: Seq<char>, str: String) -> bool {
    forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> 
    sub != str@.subrange(i, i + sub.len())
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub@, str)
    ensures !res <==> isNotSubstringPred(sub@, str)
{
    if sub.len() > str.len() {
        assert(isNotSubstringPred(sub@, str));
        return false;
    }
    
    let mut i: usize = 0;
    while i + sub.len() <= str.len()
        invariant 0 <= i <= str.len()
        invariant sub.len() <= str.len()
        invariant forall|j: int| (0 <= j < i && j + sub.len() <= str.len()) ==> 
            sub@ != str@.subrange(j, j + sub.len() as int)
    {
        if isPrefix(sub.clone(), str.clone().substring(i, str.len())) {
            assert(isPrefixPred(sub, str.substring(i, str.len())));
            assert(sub@ == str@.subrange(i as int, i as int + sub.len() as int));
            assert(isSubstringPred(sub@, str));
            return true;
        }
        assert(sub@ != str@.subrange(i as int, i as int + sub.len() as int));
        i = i + 1;
    }
    assert(forall|j: int| (0 <= j && j + sub.len() <= str.len()) ==> 
        sub@ != str@.subrange(j, j + sub.len() as int));
    assert(isNotSubstringPred(sub@, str));
    false
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
        invariant forall|j: int| (0 <= j < i) ==> pre@[j] == str@[j]
    {
        if pre.as_bytes()[i] != str.as_bytes()[i] {
            assert(exists|k: int| 0 <= k < pre.len() && pre@[k] != str@[k]);
            assert(pre@ != str@.subrange(0, pre.len() as int));
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i = i + 1;
    }
    assert(pre.len() <= str.len());
    assert(forall|j: int| (0 <= j < pre.len()) ==> pre@[j] == str@[j]);
    assert(pre@ == str@.subrange(0, pre.len() as int));
    assert(isPrefixPred(pre, str));
    true
}

fn haveCommonKSubstring(k: nat, str1: String, str2: String) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        return false;
    }
    
    let mut i: usize = 0;
    while i + k <= str1.len()
        invariant 0 <= i <= str1.len()
        invariant k <= str1.len()
        invariant forall|j: int| (0 <= j < i && j + k <= str1.len()) ==> 
            isNotSubstringPred(str1@.subrange(j, j + k as int), str2)
    {
        let substring = str1.substring(i, i + k);
        if isSubstring(substring.clone(), str2.clone()) {
            assert(isSubstringPred(substring@, str2));
            assert(substring@ == str1@.subrange(i as int, i as int + k as int));
            assert(isSubstringPred(str1@.subrange(i as int, i as int + k as int), str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        assert(isNotSubstringPred(substring@, str2));
        assert(substring@ == str1@.subrange(i as int, i as int + k as int));
        assert(isNotSubstringPred(str1@.subrange(i as int, i as int + k as int), str2));
        i = i + 1;
    }
    assert(forall|j: int| (0 <= j && j + k <= str1.len()) ==> 
        isNotSubstringPred(str1@.subrange(j, j + k as int), str2));
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    false
}

}