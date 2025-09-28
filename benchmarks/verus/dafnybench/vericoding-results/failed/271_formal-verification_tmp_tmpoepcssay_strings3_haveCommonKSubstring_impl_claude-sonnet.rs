use vstd::prelude::*;

verus! {

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
    assume(false);
    true
}



spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        res ==> isSubstringPred(sub, str),
        // ensures  !res ==> !isSubstringPred(sub, str)
        isSubstringPred(sub, str) ==> res,
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    true
}



spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_isPrefix_correct(pre: Seq<char>, str: Seq<char>)
    ensures isPrefixPred(pre, str) <==> ((pre.len() <= str.len()) && (forall|i: int| 0 <= i < pre.len() ==> pre[i] == str[i]))
{
    if isPrefixPred(pre, str) {
        assert(pre == str.subrange(0, pre.len() as int));
        assert(forall|i: int| 0 <= i < pre.len() ==> pre[i] == str.subrange(0, pre.len() as int)[i]);
        assert(forall|i: int| 0 <= i < pre.len() ==> pre[i] == str[i]);
    }
    if (pre.len() <= str.len()) && (forall|i: int| 0 <= i < pre.len() ==> pre[i] == str[i]) {
        assert(pre =~= str.subrange(0, pre.len() as int));
    }
}

proof fn lemma_substring_equiv(sub: Seq<char>, str: Seq<char>)
    ensures isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str) == false
    ensures isNotSubstringPred(sub, str) <==> isSubstringPred(sub, str) == false
{
}

proof fn lemma_common_k_substring_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2) == false
    ensures haveNotCommonKSubstringPred(k, str1, str2) <==> haveCommonKSubstringPred(k, str1, str2) == false
{
}
// </vc-helpers>

// <vc-spec>
fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2),
        !found <==> haveNotCommonKSubstringPred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        assert(isPrefixPred(str1.subrange(0, 0), str2));
        assert(isSubstringPred(str1.subrange(0, 0), str2));
        assert(haveCommonKSubstringPred(k, str1, str2));
        return true;
    }
    
    if str1.len() < k {
        assert(forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> false);
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        return false;
    }
    
    let mut i = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|i1: int| 0 <= i1 < i ==> isNotSubstringPred(str1.subrange(i1, i1 + k), str2),
    {
        let sub = str1.subrange(i as int, i + k);
        let found_sub = isSubstring(sub, str2);
        
        if found_sub {
            assert(isSubstringPred(sub, str2));
            assert(isSubstringPred(str1.subrange(i as int, i + k), str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
            return true;
        }
        
        assert(isNotSubstringPred(str1.subrange(i as int, i + k), str2));
        i = i + 1;
    }
    
    assert(forall|i1: int| 0 <= i1 <= str1.len() - k ==> isNotSubstringPred(str1.subrange(i1, i1 + k), str2));
    assert(haveNotCommonKSubstringPred(k, str1, str2));
    
    proof {
        lemma_common_k_substring_equiv(k, str1, str2);
    }
    
    false
}
// </vc-code>

fn main() {}

}