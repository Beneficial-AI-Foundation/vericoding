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
proof fn lemma_common_k_substring_equivalence(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2),
{
    if !haveCommonKSubstringPred(k, str1, str2) {
        assert forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k implies !isSubstringPred(str1.subrange(i1, j1), str2) by {
            if isSubstringPred(str1.subrange(i1, j1), str2) {
                assert(haveCommonKSubstringPred(k, str1, str2));
            }
        }
        assert forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k implies isNotSubstringPred(str1.subrange(i1, j1), str2) by {
            lemma_substring_not_equivalence(str1.subrange(i1, j1), str2);
        }
    } else {
        let i1_witness = choose|i1: int| 0 <= i1 <= str1.len() - k && isSubstringPred(str1.subrange(i1, i1 + k), str2);
        assert(0 <= i1_witness <= str1.len() - k);
        assert(isSubstringPred(str1.subrange(i1_witness, i1_witness + k), str2));
        lemma_substring_not_equivalence(str1.subrange(i1_witness, i1_witness + k), str2);
        assert(!isNotSubstringPred(str1.subrange(i1_witness, i1_witness + k), str2));
        assert(!haveNotCommonKSubstringPred(k, str1, str2));
    }
}

proof fn lemma_substring_not_equivalence(sub: Seq<char>, str: Seq<char>)
    ensures
        !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str),
{
    if !isSubstringPred(sub, str) {
        assert forall|i: int| 0 <= i <= str.len() implies !isPrefixPred(sub, str.subrange(i, str.len() as int)) by {
            if isPrefixPred(sub, str.subrange(i, str.len() as int)) {
                assert(isSubstringPred(sub, str));
            }
        }
        assert forall|i: int| 0 <= i <= str.len() implies isNotPrefixPred(sub, str.subrange(i, str.len() as int)) by {
            lemma_prefix_not_equivalence(sub, str.subrange(i, str.len() as int));
        }
    } else {
        let i_witness = choose|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int));
        assert(0 <= i_witness <= str.len());
        assert(isPrefixPred(sub, str.subrange(i_witness, str.len() as int)));
        lemma_prefix_not_equivalence(sub, str.subrange(i_witness, str.len() as int));
        assert(!isNotPrefixPred(sub, str.subrange(i_witness, str.len() as int)));
        assert(!isNotSubstringPred(sub, str));
    }
}

proof fn lemma_prefix_not_equivalence(pre: Seq<char>, str: Seq<char>)
    ensures
        !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str),
{
    // This is trivial by definition
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
    if k > str1.len() {
        proof {
            lemma_common_k_substring_equivalence(k, str1, str2);
            assert(haveNotCommonKSubstringPred(k, str1, str2));
        }
        return false;
    }

    let mut i1: usize = 0;
    while i1 <= (str1.len() - k) as usize
        invariant
            0 <= i1 <= str1.len() - k + 1,
            k <= str1.len(),
            forall|ii: int, jj: int| 0 <= ii < i1 && jj == ii + k ==> isNotSubstringPred(str1.subrange(ii, jj), str2),
    {
        let j1: usize = i1 + k as usize;
        let substring = str1.subrange(i1 as int, j1 as int);
        
        if isSubstring(substring, str2) {
            proof {
                assert(0 <= i1 as int <= str1.len() - k);
                assert(j1 as int == i1 as int + k);
                assert(isSubstringPred(str1.subrange(i1 as int, j1 as int), str2));
                assert(haveCommonKSubstringPred(k, str1, str2));
                lemma_common_k_substring_equivalence(k, str1, str2);
            }
            return true;
        }
        
        assert(isNotSubstringPred(substring, str2));
        i1 = i1 + 1;
    }
    
    proof {
        assert(i1 == str1.len() - k + 1);
        assert forall|ii: int, jj: int| 0 <= ii <= str1.len() - k && jj == ii + k implies isNotSubstringPred(str1.subrange(ii, jj), str2) by {
            assert(0 <= ii < str1.len() - k + 1);
        }
        assert(haveNotCommonKSubstringPred(k, str1, str2));
        lemma_common_k_substring_equivalence(k, str1, str2);
    }
    false
}
// </vc-code>

fn main() {}

}