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
proof fn lemma_isNotPrefix_iff(pre: Seq<char>, str: Seq<char>)
    ensures
        isNotPrefixPred(pre, str) <==> !isPrefixPred(pre, str),
{
}

proof fn lemma_isNotSubstring_iff(sub: Seq<char>, str: Seq<char>)
    ensures
        isNotSubstringPred(sub, str) <==> !isSubstringPred(sub, str),
{
}

proof fn lemma_haveNotCommonKSubstring_iff(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        haveNotCommonKSubstringPred(k, str1, str2) <==> !haveCommonKSubstringPred(k, str1, str2),
{
}

proof fn lemma_subrange_length_calculation(i: usize, k: usize) -> (res: (int, int))
    ensures
        res.0 == i as int && res.1 == i as int + k as int,
{
    (i as int, i as int + k as int)
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
    proof {
        lemma_haveNotCommonKSubstring_iff(k, str1, str2);
    }
    
    if str1.len() < k {
        proof {
            assert(!haveCommonKSubstringPred(k, str1, str2));
        }
        return false;
    }
    
    let mut i: usize = 0;
    let len_usize: usize = str1.len();
    let k_usize: usize = k;
    
    while i <= len_usize - k_usize
        invariant
            0 <= i <= len_usize - k_usize + 1,
            haveNotCommonKSubstringPred(k, str1, str2) ==> (forall|j: int| 0 <= j < i as int ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2)),
        decreases (len_usize - k_usize) - i,
    {
        proof {
            let (start, end) = lemma_subrange_length_calculation(i, k_usize);
        }
        let substr = str1.subrange(i as int, i as int + k as int);
        let found = isSubstring(substr, str2);
        if found {
            proof {
                assert(haveCommonKSubstringPred(k, str1, str2));
            }
            return true;
        }
        i = i + 1;
    }
    
    proof {
        assert(haveNotCommonKSubstringPred(k, str1, str2));
    }
    false
}
// </vc-code>

fn main() {}

}