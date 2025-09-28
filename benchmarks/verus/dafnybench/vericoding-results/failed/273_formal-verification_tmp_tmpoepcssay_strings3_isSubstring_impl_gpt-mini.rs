use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    true
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
// Helper lemmas relating subranges and prefix predicates

proof fn eq_implies_is_prefix(sub: Seq<char>, s: Seq<char>, i: int)
    requires 0 <= i && i + (sub.len() as int) <= s.len() as int;
    requires sub == s.subrange(i, i + (sub.len() as int));
    ensures is_prefix_pred(sub, s.subrange(i, s.len() as int))
{
    let m = sub.len() as int;
    // From the precondition i + m <= s.len(), we get m <= s.len() - i
    assert(i + m <= s.len() as int);
    assert(m <= s.len() as int - i);

    // s.subrange(i, s.len()).subrange(0, m) == s.subrange(i, i+m)
    assert(s.subrange(i, s.len() as int).subrange(0, m) == s.subrange(i, i + m));
    // hence sub == s.subrange(i, s.len()).subrange(0, m)
    assert(sub == s.subrange(i, s.len() as int).subrange(0, m));
    // combine to conclude is_prefix_pred: length bound and equality to subrange(0, m)
    assert(sub.len() as int <= s.subrange(i, s.len() as int).len() as int);
    assert(sub == s.subrange(i, s.len() as int).subrange(0, m));
}

proof fn prefix_implies_eq(sub: Seq<char>, s: Seq<char>, i: int)
    requires 0 <= i && i <= s.len() as int;
    requires is_prefix_pred(sub, s.subrange(i, s.len() as int));
    ensures sub == s.subrange(i, i + (sub.len() as int))
{
    let m = sub.len() as int;
    // From is_prefix_pred we have sub == s.subrange(i,s.len()).subrange(0,m)
    assert(sub == s.subrange(i, s.len() as int).subrange(0, m));
    // And s.subrange(i,s.len()).subrange(0,m) == s.subrange(i,i+m)
    assert(s.subrange(i, s.len() as int).subrange(0, m) == s.subrange(i, i + m));
    assert(sub == s.subrange(i, i + m));
}

proof fn prefix_implies_index_bound(sub: Seq<char>, s: Seq<char>, j: int)
    requires 0 <= j && j <= s.len() as int;
    requires is_prefix_pred(sub, s.subrange(j, s.len() as int));
    ensures j <= s.len() as int - (sub.len() as int)
{
    // From is_prefix_pred we have sub.len() <= s.subrange(j, s.len()).len()
    assert((sub.len() as int) <= s.subrange(j, s.len() as int).len() as int);
    // s.subrange(j, s.len()).len() == s.len() - j
    assert((sub.len() as int) <= s.len() as int - j);
    // Rearranged gives j <= s.len() - sub.len()
    assert(j <= s.len() as int - (sub.len() as int));
}

proof fn len_gt_implies_not_prefix(sub: Seq<char>, s: Seq<char>)
    requires (sub.len() as int) > (s.len() as int);
    ensures is_not_prefix_pred(sub, s)
{
    // Directly follows from the definition of is_not_prefix_pred
    assert((sub.len() as int) > (s.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        res ==> is_substring_pred(sub, str),
        // ensures  !res ==> !is_substring_pred(sub, str)
        is_substring_pred(sub, str) ==> res,
        is_substring_pred(sub, str) ==> res,
        !res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let n = str.len() as int;
    let m = sub.len() as int;

    if m > n {
        // If sub is longer than str, it cannot be a substring.
        // Prove is_not_substring_pred holds to satisfy the postcondition when returning false.
        proof {
            // For any position k in 0..=n, the remaining length is n - k < m, so is_not_prefix_pred holds.
            assert(forall|k: int| 0 <= k && k <= n ==>
                sub.len() as int > str.subrange(k, n).len() as int);
            assert(forall|k: int| 0 <= k && k <= n ==>
                is_not_prefix_pred(sub, str.subrange(k, n)));
        }
        return false;
    }

    // Loop over possible start positions i from 0 to n - m inclusive.
    let mut i: int = 0;
    while i <= n - m
        invariant 0 <= i && i <= n - m + 1
        invariant forall|j: int| 0 <= j && j < i ==> is_not_prefix_pred(sub, str.subrange(j, n))
        decreases n - m + 1 - i
    {
        // At this point i + m <= n holds.
        if sub == str.subrange(i, i + m) {
            // From the equality we can derive the prefix property at position i.
            proof {
                eq_implies_is_prefix(sub, str, i);
                // Exhibit i as witness for is_substring_pred
                assert(exists|k: int| k == i && 0 <= k && k <= n && is_prefix_pred(sub, str.subrange(k, n)));
            }
            return true;
        } else {
            // If equality does not hold, then at position i the prefix predicate does not hold.
            proof {
                assert(sub != str.subrange(i, i + m));
                assert(str.subrange(i, n).subrange(0, m) == str.subrange(i, i + m));
                assert(sub != str.subrange(i, n).subrange(0, m));
                // Therefore is_not_prefix_pred holds at i.
                assert(is_not_prefix_pred(sub, str.subrange(i, n)));
            }
            i = i + 1;
        }
    }

    // If we exit the loop, no matching prefix was found at any i in 0..=n-m.
    // Need to show is_not_substring_pred holds: for all k in 0..=n, is_not_prefix_pred(sub, str.subrange(k, n)).
    proof {
        // From the loop invariant at exit, i == n - m + 1 and forall j < i ... holds
        assert(i == n - m + 1);
        // For any k with 0 <= k <= n, consider two cases:
        // 1) k <= n - m: then k < i, so by the loop invariant is_not_prefix_pred holds.
        // 2) k > n - m: remaining length n - k < m, so sub.len() > remaining length, hence is_not_prefix_pred.
        assert(forall|k: int| 0 <= k && k <= n ==>
            (if k <= n - m {
                is_not_prefix_pred(sub, str.subrange(k, n))
            } else {
                {
                    assert(str.subrange(k, n).len() as int == n - k);
                    assert(n - k < m);
                    assert(sub.len() as int > str.subrange(k, n).len() as int);
                    len_gt_implies_not_prefix(sub, str.subrange(k, n));
                    is_not_prefix_pred(sub, str.subrange(k, n))
                }
            }));
    }
    return false;
}
// </vc-code>

fn main() {}

}