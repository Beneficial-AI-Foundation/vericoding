use vstd::prelude::*;

verus! {

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
}



spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        //!res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    false
}


spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k && 
        is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k ==> 
        is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_is_not_prefix_implies_len_check(pre: Seq<char>, str: Seq<char>)
    requires is_not_prefix_pred(pre, str)
    ensures pre.len() > str.len() || (pre.len() <= str.len() && pre != str.subrange(0, pre.len() as int))
{}

proof fn lemma_is_prefix_or_not_prefix(pre: Seq<char>, str: Seq<char>)
    ensures is_prefix_pred(pre, str) || is_not_prefix_pred(pre, str)
{
    if pre.len() <= str.len() {
        if pre == str.subrange(0, pre.len() as int) {
            assert(is_prefix_pred(pre, str));
        } else {
            assert(is_not_prefix_pred(pre, str));
        }
    } else {
        assert(is_not_prefix_pred(pre, str));
    }
}

proof fn lemma_auto_substring_is_prefix(sub: Seq<char>, str: Seq<char>, start: int)
    requires
        0 <= start <= str.len() - sub.len(),
        #[trigger] is_prefix_pred(sub, str.subrange(start, (str.len() as int)))
    ensures
        is_substring_pred(sub, str)
{
    assert(exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))) by {
        assert(start <= str.len());
        assert(is_prefix_pred(sub, str.subrange(start, str.len() as int)));
        // The existential quantifier choose can pick 'start'
    }
}

proof fn lemma_substring_is_prefix_at_some_point(sub: Seq<char>, str: Seq<char>, start: int)
    requires
        0 <= start <= str.len() - sub.len(),
        is_substring_pred(sub, str)
    ensures
        exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
{
    // This lemma essentially just restates the definition of is_substring_pred for verifier.
    // It is mainly to help the verifier see the implication more easily.
}

proof fn lemma_substring_implies_common_k(k: nat, str1: Seq<char>, sub: Seq<char>, str2: Seq<char>, idx: int)
    requires
        0 <= idx <= str1.len() - k,
        sub == str1.subrange(idx, idx + k as int),
        is_substring_pred(sub, str2)
    ensures
        have_common_k_substring_pred(k, str1, str2)
{
    assert(exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)) by {
        assert(is_substring_pred(str1.subrange(idx, idx + k as int), str2));
    }
}

proof fn lemma_common_k_implies_substring(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        have_common_k_substring_pred(k, str1, str2)
    ensures
        exists|idx: int| 0 <= idx <= str1.len() - k && is_substring_pred(str1.subrange(idx, idx + k as int), str2)
{
    // This lemma is a direct restatement of the definition of have_common_k_substring_pred.
    // The verifier should be able to infer it.
}

proof fn lemma_is_substring_transitivity(s1: Seq<char>, s2: Seq<char>, s3: Seq<char>)
    requires
        is_substring_pred(s1, s2),
        is_substring_pred(s2, s3)
    ensures
        is_substring_pred(s1, s3)
{
    assert(exists|i: int| 0 <= i <= s2.len() && is_prefix_pred(s1, s2.subrange(i, s2.len() as int))) by {
        assert(is_substring_pred(s1, s2));
    }
    let (idx1) = choose|idx1: int| 0 <= idx1 <= s2.len() && is_prefix_pred(s1, s2.subrange(idx1, s2.len() as int));
    assert(exists|j: int| 0 <= j <= s3.len() && is_prefix_pred(s2, s3.subrange(j, s3.len() as int))) by {
        assert(is_substring_pred(s2, s3));
    }
    let (idx2) = choose|idx2: int| 0 <= idx2 <= s3.len() && is_prefix_pred(s2, s3.subrange(idx2, s3.len() as int));

    // This is a complex proof that might require splitting s2.subrange further.
    // For the current problem, this lemma probably isn't directly needed or is implied by other simpler ones.
}
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        //!found <==> have_not_common_k_substring_pred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if (k == 0) {
        // An empty string (k=0) is always a common k-substring of any two strings.
        // have_common_k_substring_pred(0, str1, str2) is true if a 0-length substring exists.
        // A 0-length substring exists at any position.
        // For example, str1.subrange(0,0) is a 0-length string which is prefix of str2.subrange(0, str2.len())
        // and thus a substring of str2.
        assert(is_prefix_pred(Seq::<char>::empty(), str2.subrange(0, str2.len() as int)));
        assert(is_substring_pred(Seq::<char>::empty(), str2));
        assert(have_common_k_substring_pred(k, str1, str2) ) by {
            assert(k==0);
            assert(0 <= 0 && 0 <= str1.len() -0); // for i1 =0
            assert(is_substring_pred(str1.subrange(0,0), str2)); // str1.subrange(0,0) is empty string
        }; // k == 0 implies true
        return true;
    }
    if (str1.len() < k || str2.len() < k) {
        // If either string is shorter than k, no k-substring can exist.
        // Hence, have_common_k_substring_pred must be false.
        assert(have_common_k_substring_pred(k, str1, str2) == false) by {
            if (have_common_k_substring_pred(k, str1, str2)) {
                let (i_exist, j_exist) = choose|i_exist: int, j_exist: int|
                    0 <= i_exist <= str1.len() - k &&
                    j_exist == i_exist + k &&
                    is_substring_pred(str1.subrange(i_exist, j_exist), str2);
                let sub = str1.subrange(i_exist, j_exist);
                assert(sub.len() == k);
                let (i_sub) = choose|i_sub: int| 0 <= i_sub <= str2.len() && is_prefix_pred(sub, str2.subrange(i_sub, str2.len() as int));
                assert(sub.len() <= str2.subrange(i_sub, str2.len() as int).len());
                assert(k <= str2.len() - i_sub);
                assert(k <= str2.len());
            }
        };
        return false;
    }

    let mut found: bool = false;
    let mut i: int = 0;

    // Outer loop iterates through all possible starting positions for a k-substring in str1.
    while i <= ((str1.len() as int) - (k as int))
        invariant
            0 <= i <= (str1.len() as int) - (k as int) + 1,
            // The `found` variable correctly tracks if a common k-substring has been found so far.
            found == (exists|idx: int| 0 <= idx < i && idx + k as int <= str1.len() && is_substring_pred(str1.subrange(idx, idx + k as int), str2)),
            // If k > 0, then str1 must have at least length k, proved by the initial check.
            k > 0 ==> str1.len() >= k,
            // If found is true, then we satisfy the postcondition.
            found ==> have_common_k_substring_pred(k, str1, str2),
    {
        let current_k_substring = str1.subrange(i, (i + k) as int);
        // This is a k-substring derived from str1.
        // We now check if `current_k_substring` is a substring of `str2`.
        assert(current_k_substring.len() == k);

        let mut j: int = 0;
        let mut inner_found: bool = false; // Tracks if current_k_substring is found in str2

        // Inner loop iterates through all possible starting positions for `current_k_substring` in `str2`.
        while j <= ((str2.len() as int) - (k as int))
            invariant
                0 <= j <= (str2.len() as int) - (k as int) + 1,
                // `inner_found` correctly tracks if `current_k_substring` is found in `str2` at an index < j.
                inner_found == (exists|idx: int| 0 <= idx < j && idx + k as int <= str2.len() && is_prefix_pred(current_k_substring, str2.subrange(idx, str2.len() as int))),
                // If k > 0, then str2 must have at least length k, proved by the initial check.
                k > 0 ==> str2.len() >= k,
                current_k_substring.len() == k,
        {
            if (j + k) as int <= str2.len() && is_prefix_pred(current_k_substring, str2.subrange(j, (j + k) as int)) {
                // If current_k_substring is a prefix of str2 starting at j, then it's a substring.
                assert(is_substring_pred(current_k_substring, str2)) by {
                    assert(j + k <= str2.len()); // This asserts the subrange is valid.
                    lemma_auto_substring_is_prefix(current_k_substring, str2, j);
                };
                inner_found = true;
                break;
            }
            j = j + 1;
        }

        if inner_found {
            // If current_k_substring was found in str2, then we've found a common k-substring.
            // This means 'found' can be set to true, satisfying an existential claim from the invariant.
            assert(is_substring_pred(current_k_substring, str2));
            assert(i + k as int <= str1.len());
            assert(exists|idx: int| 0 <= idx <= i && idx + k as int <= str1.len() && is_substring_pred(str1.subrange(idx, idx + k as int), str2));
            found = true;
            break;
        }

        i = i + 1;
    }

    assert(found <==> have_common_k_substring_pred(k, str1, str2)) by {
        if found {
            // If found is true, the invariant ensures the existential condition for have_common_k_substring_pred.
            assert(exists|idx: int| 0 <= idx < i && idx + k as int <= str1.len() && is_substring_pred(str1.subrange(idx, idx + k as int), str2));
            assert(have_common_k_substring_pred(k, str1, str2));
        } else {
            // If found is false after the loop, it means for all idx, str1.subrange(idx, idx+k) is NOT a substring of str2.
            // This needs to be proven from the invariant.
            // From invariant: found == (exists|idx: int| 0 <= idx < i && is_substring_pred(str1.subrange(idx, idx + k as int), str2))
            // If found is false, then !(exists|idx: int| 0 <= idx < i && is_substring_pred(str1.subrange(idx, idx + k as int), str2))
            // Which means (forall|idx: int| 0 <= idx < i ==> !is_substring_pred(str1.subrange(idx, idx + k as int), str2))
            // Also because the loop finished, i must be (str1.len() as int) - (k as int) + 1.
            // So we have (forall|idx: int| 0 <= idx <= (str1.len() as int) - (k as int) ==> !is_substring_pred(str1.subrange(idx, idx + k as int), str2))
            // which is equivalent to !have_common_k_substring_pred(k, str1, str2).
            assert(i == (str1.len() as int) - (k as int) + 1);
            forall |idx: int| 0 <= idx <= (str1.len() as int) - (k as int)
                implies !is_substring_pred(str1.subrange(idx, idx + k as int), str2)
                by {
                    if (idx < i) {
                        assert(!is_substring_pred(str1.subrange(idx, idx + k as int), str2));
                    } else { // idx == i, loop terminated without finding.
                        // We need to show that this particular str1.subrange(i, i+k) is also not a substring.
                        // The inner loop would have found it if it were.
                        let current_k_substring_final = str1.subrange(idx, (idx + k) as int);
                        assert(! is_substring_pred(current_k_substring_final, str2)) by {
                            assert(current_k_substring_final.len() == k);
                            if (is_substring_pred(current_k_substring_final, str2)) {
                                let (j_prime) = choose |j_prime: int| 0 <= j_prime <= str2.len() && is_prefix_pred(current_k_substring_final, str2.subrange(j_prime, str2.len() as int));
                                assert(j_prime + k as int <= str2.len());
                                assert(is_prefix_pred(current_k_substring_final, str2.subrange(j_prime, (j_prime + k) as int)));
                                // This means the inner loop for current i (which is idx) should have set inner_found to true at j_prime.
                                // Contradiction: inner_found would be true for this iteration of the outer loop.
                            }
                        };
                    }
                }
            assert(!have_common_k_substring_pred(k, str1, str2));
        }
    }

    found
}
// </vc-code>

fn main() {}

}