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
    exists|i1: int, j1: int| 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && 
    isSubstringPred(str1.spec_index(i1..j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int, j1: int| (0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k) ==> 
    isNotSubstringPred(str1.spec_index(i1..j1), str2)
}

spec fn isSubstringPred(sub: String, str: String) -> bool {
    exists|i: int| 0 <= i && i <= str.len() && isPrefixPred(sub, str.spec_index(i..))
}

spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) || 
    pre != str.spec_index(..pre.len() as int)
}

spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    forall|i: int| (0 <= i && i <= str.len()) ==> isNotPrefixPred(sub, str.spec_index(i..))
}

fn isSubstring(sub: String, str: String) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
    ensures !res <==> isNotSubstringPred(sub, str)
{
    let mut i: usize = 0;
    while i <= str.len()
        invariant 0 <= i <= str.len() + 1
        invariant forall|j: int| (0 <= j < i) ==> isNotPrefixPred(sub, str.spec_index(j..))
    {
        if isPrefix(sub, str.spec_index(i as int..)) {
            assert(isPrefixPred(sub, str.spec_index(i as int..)));
            assert(isSubstringPred(sub, str));
            return true;
        }
        assert(isNotPrefixPred(sub, str.spec_index(i as int..)));
        i = i + 1;
    }
    assert(forall|j: int| (0 <= j <= str.len()) ==> isNotPrefixPred(sub, str.spec_index(j..)));
    assert(isNotSubstringPred(sub, str));
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
        invariant i <= str.len()
        invariant forall|j: int| (0 <= j < i) ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1)
    {
        if pre.spec_index(i as int..i as int + 1) != str.spec_index(i as int..i as int + 1) {
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i = i + 1;
    }
    assert(pre.len() <= str.len());
    assert(forall|j: int| (0 <= j < pre.len()) ==> pre.spec_index(j..j+1) == str.spec_index(j..j+1));
    assert(pre == str.spec_index(..pre.len() as int));
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
        invariant 0 <= i <= str1.len() - k + 1
        invariant forall|j: int| (0 <= j < i && j + k <= str1.len()) ==> 
            isNotSubstringPred(str1.spec_index(j..j + k as int), str2)
    {
        let substring = str1.spec_index(i as int..i as int + k as int);
        if isSubstring(substring, str2) {
            assert(isSubstringPred(substring, str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        assert(isNotSubstringPred(substring, str2));
        i = i + 1;
    }
    assert(forall|j: int| (0 <= j && j + k <= str1.len()) ==> 
        isNotSubstringPred(str1.spec_index(j..j + k as int), str2));
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    false
}

}