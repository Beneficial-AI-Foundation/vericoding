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

// Helper lemma to establish the relationship between substring predicates
proof fn lemma_substring_negation(sub: Seq<char>, str: Seq<char>)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
{
    // The proof is automatic for this logical equivalence
}

// Helper lemma to establish the relationship between haveCommonKSubstringPred and haveNotCommonKSubstringPred
proof fn lemma_common_substring_negation(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
{
    // The proof follows from the logical equivalence of exists and forall negation
    assert forall|i1: int| #![auto] (0 <= i1 && i1 + k as int <= str1.len()) ==> 
        (isSubstringPred(str1.subrange(i1, i1 + k as int), str2) <==> !isNotSubstringPred(str1.subrange(i1, i1 + k as int), str2))
    by {
        lemma_substring_negation(str1.subrange(i1, i1 + k as int), str2);
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
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
            forall|j: int| 0 <= j < i ==> !isPrefixPred(sub, str.subrange(j, j + sub.len()))
        decreases str.len() - i
    {
        let suffix = str.subrange(i as int, i as int + sub.len());
        let is_prefix = isPrefix(sub, suffix);
        if is_prefix {
            assert(isPrefixPred(sub, str.subrange(i as int, i as int + sub.len())));
            return true;
        }
        i += 1;
    }
    
    false
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
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
            forall|k: int| 0 <= k < i ==> pre[k] == str[k]
        decreases pre.len() - i
    {
        if pre[i as int] != str[i as int] {
            return false;
        }
        i += 1;
    }
    
    // Prove that pre equals str.subrange(0, pre.len())
    assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == str.subrange(0, pre.len() as int)[k]);
    assert(pre.len() == str.subrange(0, pre.len() as int).len());
    assert(pre =~= str.subrange(0, pre.len() as int));
    true
}

fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k > 0
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
    if k > str1.len() {
        proof {
            lemma_common_substring_negation(k, str1, str2);
        }
        return false;
    }
    
    let mut i: usize = 0;
    while i + k <= str1.len()
        invariant 
            0 <= i <= str1.len(),
            k <= str1.len(),
            k > 0,
            forall|j: int| 0 <= j < i ==> !isSubstringPred(str1.subrange(j, j + k as int), str2)
        decreases str1.len() - i
    {
        let substring = str1.subrange(i as int, i as int + k as int);
        let is_common = isSubstring(substring, str2);
        if is_common {
            return true;
        }
        i += 1;
    }
    
    proof {
        lemma_common_substring_negation(k, str1, str2);
    }
    false
}

}