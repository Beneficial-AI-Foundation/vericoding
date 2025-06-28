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
    exists|i1: int| 0 <= i1 && i1 + k as int <= str1.len() && isSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int| (0 <= i1 && i1 + k as int <= str1.len()) ==> isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i && i + sub.len() <= str.len() && isPrefixPred(sub, str.subrange(i, i + sub.len()))
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(i, i + sub.len()))
}

// Helper lemma to establish the relationship between haveCommonKSubstringPred and haveNotCommonKSubstringPred
proof fn lemma_common_substring_negation(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
{
    if haveCommonKSubstringPred(k, str1, str2) {
        // If there exists a common substring, then it's not the case that all substrings are not common
        let i1 = choose|i1: int| 0 <= i1 && i1 + k as int <= str1.len() && isSubstringPred(str1.subrange(i1, i1 + k as int), str2);
        assert(!isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2));
        assert(!haveNotCommonKSubstringPred(k, str1, str2));
    }
    
    if !haveNotCommonKSubstringPred(k, str1, str2) {
        // If it's not the case that all substrings are not common, then there exists a common substring
        let i1 = choose|i1: int| 0 <= i1 && i1 + k as int <= str1.len() && !isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2);
        assert(isSubstringPred(str1.subrange(i1, i1 + k as int), str2));
        assert(haveCommonKSubstringPred(k, str1, str2));
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> isSubstringPred(sub, str)
{
    if sub.len() > str.len() {
        assert(forall|i: int| (0 <= i && i + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(i, i + sub.len()))) by {
            // Empty range - vacuously true since sub.len() > str.len() means no valid i
        }
        assert(isNotSubstringPred(sub, str));
        return false;
    }
    
    let mut i: usize = 0;
    while i + sub.len() <= str.len()
        invariant 
            0 <= i <= str.len(),
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, j + sub.len()))
        decreases str.len() - i
    {
        let suffix = str.subrange(i as int, i as int + sub.len());
        let is_prefix = isPrefix(sub, suffix);
        if is_prefix {
            assert(isPrefixPred(sub, str.subrange(i as int, i as int + sub.len())));
            assert(isSubstringPred(sub, str)) by {
                assert(0 <= i as int && i as int + sub.len() <= str.len());
                assert(isPrefixPred(sub, str.subrange(i as int, i as int + sub.len())));
            }
            return true;
        }
        assert(isNotPrefixPred(sub, str.subrange(i as int, i as int + sub.len())));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + sub.len() <= str.len()) ==> isNotPrefixPred(sub, str.subrange(j, j + sub.len()))) by {
        assert(forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, j + sub.len())));
        assert(i + sub.len() > str.len());
        // For j >= i, we have j + sub.len() > str.len(), so the condition is false
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
                assert(str.subrange(0, pre.len() as int)[i as int] == str[i as int]);
            }
            assert(isNotPrefixPred(pre, str));
            return false;
        }
        i += 1;
    }
    
    assert(pre == str.subrange(0, pre.len() as int)) by {
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str[k]);
        assert(pre.len() == str.subrange(0, pre.len() as int).len());
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str.subrange(0, pre.len() as int)[k]) by {
            assert(forall|k: int| 0 <= k < pre.len() ==> str.subrange(0, pre.len() as int)[k] == str[k]);
        }
    }
    assert(isPrefixPred(pre, str));
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        assert(forall|j: int| (0 <= j && j + k as int <= str1.len()) ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)) by {
            // Empty range - vacuously true since k > str1.len()
        }
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        proof {
            lemma_common_substring_negation(k, str1, str2);
        }
        assert(!haveCommonKSubstringPred(k, str1, str2));
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
                assert(0 <= i as int && i as int + k as int <= str1.len());
                assert(isSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
            }
            return true;
        }
        assert(isNotSubstringPred(str1.subrange(i as int, i as int + k as int), str2));
        i += 1;
    }
    
    assert(forall|j: int| (0 <= j && j + k as int <= str1.len()) ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)) by {
        assert(forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2));
        assert(i + k > str1.len());
        // For j >= i, we have j + k as int > str1.len(), so the condition is false
    }
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    proof {
        lemma_common_substring_negation(k, str1, str2);
    }
    assert(!haveCommonKSubstringPred(k, str1, str2));
    false
}

}