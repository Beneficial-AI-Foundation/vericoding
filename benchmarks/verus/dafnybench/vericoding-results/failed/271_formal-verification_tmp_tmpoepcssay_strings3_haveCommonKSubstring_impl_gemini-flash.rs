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
lemma fn lemma_isPrefixPred_properties(pre: Seq<char>, str: Seq<char>)
    ensures
        isPrefixPred(pre, str) <==> ((pre.len() <= str.len()) && pre == str.subrange(0, pre.len() as int)),
        isNotPrefixPred(pre, str) <==> ((pre.len() > str.len()) || pre != str.subrange(0, pre.len() as int)),
        !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str),
        isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str),
{
    // These are direct definitions.
}

lemma fn lemma_isSubstringPred_properties(sub: Seq<char>, str: Seq<char>)
    ensures
        isSubstringPred(sub, str) <==> (exists|i: int| 0 <= i as int <= str.len() && #[trigger] isPrefixPred(sub, str.subrange(i, str.len() as int))),
        isNotSubstringPred(sub, str) <==> (forall|i: int| 0 <= i as int <= str.len() ==> #[trigger] isNotPrefixPred(sub, str.subrange(i, str.len() as int))),
        !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str),
{
    // These are direct definitions or easily proven from definitions.
}

// Re-implementing isPrefix and isSubstring to correctly verify the helper predicates
fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
    let result = (pre.len() <= str.len()) && pre == str.subrange(0, pre.len() as int);
    proof {
        lemma_isPrefixPred_properties(pre, str);
    }
    result
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        !res <==> isNotSubstringPred(sub, str),
{
    if sub.len() == 0 {
        return true; // Empty string is a substring of any string.
    }
    if sub.len() > str.len() {
        return false;
    }

    let mut i: int = 0;
    let mut found = false;

    while i <= (str.len() - sub.len())
        invariant
            0 <= i <= (str.len() - sub.len() + 1),
            found == (exists|j: int| 0 <= j < i && #[trigger] isPrefixPred(sub, str.subrange(j, str.len() as int))),
            !found ==> (forall|j: int| 0 <= j < i ==> #[trigger] isNotPrefixPred(sub, str.subrange(j, str.len() as int))),
            sub.len() <= str.len(),
    {
        let current_str_slice = str.subrange(i, str.len() as int);
        
        let local_is_prefix = isPrefix(sub, current_str_slice);

        if local_is_prefix {
            found = true;
            break;
        }
        i = i + 1;
    }

    proof {
        if found {
            assert(exists|j: int| 0 <= j < i && isPrefixPred(sub, str.subrange(j, str.len() as int)));
            assert(isSubstringPred(sub, str));
        } else {
            assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
            // The upper bound for j in the predicate is str.len(), not str.len() - sub.len()
            assert(forall|j: int| 0 <= j <= str.len() ==> #[trigger] isNotPrefixPred(sub, str.subrange(j, str.len() as int)) || j > str.len() - sub.len());
            // Need to show that for j strictly greater than str.len() - sub.len(), isNotPrefixPred(sub, str.subrange(j, str.len() as int)) also holds.
            // This is because sub.len() > str.subrange(j, str.len() as int).len() for such j.
            // If sub.len() > str.subrange(j, str.len() as int).len(), then it's a non-prefix.
            forall |j: int| 0 <= j <= str.len()
                implies isNotPrefixPred(sub, str.subrange(j, str.len() as int)) by {
                if j <= str.len() - sub.len() {
                    // This case is covered by the loop invariant when !found
                    assert(isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
                } else {
                    // j > str.len() - sub.len()
                    // This means (str.len() - j) < sub.len()
                    // str.subrange(j, str.len() as int) has length (str.len() - j)
                    assert(str.subrange(j, str.len() as int).len() == str.len() - j);
                    assert(sub.len() > str.len() - j);
                    assert(sub.len() > str.subrange(j, str.len() as int).len());
                    // By definition of isNotPrefixPred, if pre.len() > str.len(), then it's a non-prefix.
                    lemma_isPrefixPred_properties(sub, str.subrange(j, str.len() as int));
                    assert(isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
                }
            }
            assert(isNotSubstringPred(sub, str));
        }
        lemma_isSubstringPred_properties(sub, str);
    }
    found
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
        // According to the spec, for k=0, any string contains an empty k-substring.
        // It means there exists i1, j1 such that j1 = i1 + 0, which means i1 = j1.
        // And isSubstringPred(str1.subrange(i1, i1), str2) is true.
        // str1.subrange(i1, i1) is an empty sequence.
        // isSubstringPred(empty_seq, any_seq) is true, because isPrefixPred(empty_seq, any_seq) is true.
        // isPrefixPred(empty_seq, s) => empty_seq.len() <= s.len() (True, 0 <= s.len()) AND empty_seq == s.subrange(0,0) (True).
        // So, for k=0, haveCommonKSubstringPred is always true.
        proof {
            assert(haveCommonKSubstringPred(0, str1, str2));
        }
        return true;
    }

    if k as int > str1.len() {
        proof {
            assert(haveNotCommonKSubstringPred(k, str1, str2));
        }
        return false;
    }

    let mut i1: int = 0;
    let mut found = false;

    while i1 <= (str1.len() - k as int)
        invariant
            0 <= i1 <= (str1.len() - k as int + 1),
            found == (exists|prev_i1: int| 0 <= prev_i1 < i1 && prev_i1 + k as int <= str1.len() && #[trigger] isSubstringPred(str1.subrange(prev_i1, prev_i1 + k as int), str2)),
            !found ==> (forall|prev_i1: int| 0 <= prev_i1 < i1 && prev_i1 + k as int <= str1.len() ==> #[trigger] isNotSubstringPred(str1.subrange(prev_i1, prev_i1 + k as int), str2)),
            k as int <= str1.len(), // From the initial check
    {
        let j1 = i1 + k as int;
        proof {
            assert(0 <= i1);
            assert(j1 == i1 + k as int);
            assert(j1 <= str1.len()); 
        }

        let sub_str1 = str1.subrange(i1, j1);
        let current_is_substring = isSubstring(sub_str1, str2);

        if current_is_substring {
            found = true;
            break;
        }
        i1 = i1 + 1;
    }

    proof {
        if found {
            assert(exists|prev_i1: int| 0 <= prev_i1 < i1 && prev_i1 + k as int <= str1.len() && isSubstringPred(str1.subrange(prev_i1, prev_i1 + k as int), str2));
            assert(haveCommonKSubstringPred(k, str1, str2));
        } else {
            // Need to prove that for all possible (i1, j1) pairs, they do not form a common k-substring.
            // The loop invariant covers i1 < current_i. We need to extend this to 
            // the full range 0 <= i1 <= str1.len() - k.
            forall |idx: int| 0 <= idx <= str1.len() - k as int
                implies isNotSubstringPred(str1.subrange(idx, idx + k as int), str2) by {
                // If the loop finished without finding, it means for all i1 in [0, str1.len() - k],
                // isSubstring(str1.subrange(i1, i1+k), str2) was false.
                // By the postcondition of isSubstring, this implies isNotSubstringPred.
                let temp_sub = str1.subrange(idx, idx + k as int);
                assert(!isSubstring(temp_sub, str2)); // This is what the loop implies
                assert(isNotSubstringPred(temp_sub, str2)); // By isSubstring's postcondition
            }
            assert(haveNotCommonKSubstringPred(k, str1, str2));
        }
    }
    found
}
// </vc-code>

fn main() {}

}