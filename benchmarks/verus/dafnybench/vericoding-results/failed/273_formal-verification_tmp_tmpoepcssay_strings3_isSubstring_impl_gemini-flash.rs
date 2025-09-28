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
spec fn is_substring_at_pred(sub: Seq<char>, str: Seq<char>, i: int) -> bool {
    0 <= i && (i as nat) + sub.len() <= str.len() &&
    str.subrange(i, (i as nat + sub.len()) as int) == sub
}

proof fn lemma_is_substring_at_iff_is_prefix_at_offset(sub: Seq<char>, str: Seq<char>, i: int)
    requires
        0 <= i,
        (i as nat) + sub.len() <= str.len(),
    ensures
        is_substring_at_pred(sub, str, i) <==>
            is_prefix_pred(sub, str.subrange(i, str.len() as int)),
{
    // This lemma establishes the equivalence between `is_substring_at_pred`
    // and `is_prefix_pred` applied to a subrange of `str`.
    // It's a direct consequence of the definitions.
}

proof fn lemma_is_substring_iff_exists_is_substring_at(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) <==>
            (exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i))
{
    // Direction 1: is_substring_pred ==> exists i such that is_substring_at_pred
    if is_substring_pred(sub, str) {
        let (i_orig) = choose|i_orig: int| 0 <= i_orig && (i_orig as nat) <= str.len() && is_prefix_pred(sub, str.subrange(i_orig, str.len() as int));
        assert(is_prefix_pred(sub, str.subrange(i_orig, str.len() as int)));
        assert(sub.len() <= str.subrange(i_orig, str.len() as int).len());
        assert(str.subrange(i_orig, str.len() as int).subrange(0, sub.len() as int) == sub);
        assert(str.subrange(i_orig, (i_orig as nat + sub.len()) as int) == sub);
        assert((i_orig as nat) + sub.len() <= str.len());
        assert(is_substring_at_pred(sub, str, i_orig)); // Direct application of definition
        assert(exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i));
    }

    // Direction 2: (exists i such that is_substring_at_pred) ==> is_substring_pred
    if (exists|i_found_ex: int| 0 <= i_found_ex && (i_found_ex as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i_found_ex)) {
        let (i_found) = choose|i_found: int| 0 <= i_found && (i_found as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i_found);
        assert(is_substring_at_pred(sub, str, i_found));
        assert(str.subrange(i_found, (i_found as nat + sub.len()) as int) == sub);
        assert(is_prefix_pred(sub, str.subrange(i_found, str.len() as int)));
        assert(is_substring_pred(sub, str));
    }
}

proof fn lemma_is_not_substring_iff_forall_not_is_substring_at(sub: Seq<char>, str: Seq<char>)
    ensures
        is_not_substring_pred(sub, str) <==>
            (forall|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() ==> !is_substring_at_pred(sub, str, i))
{
    // This lemma connects is_not_substring_pred with the negation of is_substring_at_predforall.
    // It's derived from the definitions and De Morgan's laws for quantifiers.
    // From lemma_is_substring_iff_exists_is_substring_at, we have
    // is_substring_pred(sub, str) <==> (exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i))
    // Taking the negation of both sides:
    // !is_substring_pred(sub, str) <==> !(exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i))
    // Using is_not_substring_pred for !is_substring_pred:
    // is_not_substring_pred(sub, str) <==> (forall|i: int| !(0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i)))
    //                                  <==> (forall|i: int| !(0 <= i && (i as nat) <= str.len() - sub.len()) || !is_substring_at_pred(sub, str, i))
    //                                  <==> (forall|i: int| (0 > i || (i as nat) > str.len() - sub.len()) || !is_substring_at_pred(sub, str, i))
    // Which is logically equivalent to:
    // is_not_substring_pred(sub, str) <==> (forall|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() ==> !is_substring_at_pred(sub, str, i))
    lemma_is_substring_iff_exists_is_substring_at(sub, str);
    if is_not_substring_pred(sub, str) {
        assert(!is_substring_pred(sub, str));
        assert(forall|i: int| !(0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i)));
        assert(forall|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() ==> !is_substring_at_pred(sub, str, i));
    } else {
        assert(!is_not_substring_pred(sub, str));
        assert(is_substring_pred(sub, str));
        assert(exists|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() && is_substring_at_pred(sub, str, i));
        assert(!(forall|i: int| 0 <= i && (i as nat) <= str.len() - sub.len() ==> !is_substring_at_pred(sub, str, i)));
    }
}

proof fn lemma_is_prefix_true_implies_subrange_true(pre: Seq<char>, str: Seq<char>, start: int)
    requires
        is_prefix_pred(pre, str.subrange(start, str.len() as int)),
    ensures
        str.subrange(start, (start as nat + pre.len()) as int) == pre,
        (start as nat + pre.len()) <= str.len(),
    {
        assert(pre.len() <= str.subrange(start, str.len() as int).len());
        assert((start as nat + pre.len()) <= str.len());
        assert(pre == str.subrange(start, str.len() as int).subrange(0, pre.len() as int));
        assert(str.subrange(start, (start as nat + pre.len()) as int) == pre);
    }

proof fn lemma_is_not_prefix_true_implies_subrange_false(pre: Seq<char>, str: Seq<char>, start: int)
    requires
        is_not_prefix_pred(pre, str.subrange(start, str.len() as int)),
    ensures
        !(pre.len() <= str.subrange(start, str.len() as int).len() &&
        pre == str.subrange(start, str.len() as int).subrange(0, pre.len() as int))
    {
        // This is just a direct unwrapping of the definition of is_not_prefix_pred.
    }

proof fn lemma_is_prefix_equiv(pre: Seq<char>, s: Seq<char>)
    ensures
        is_prefix(pre, s) <==> is_prefix_pred(pre, s),
        !is_prefix(pre, s) <==> is_not_prefix_pred(pre, s),
{
    // This lemma is stated by the is_prefix function's postconditions, so we just invoke it.
    // It's needed because `is_prefix` needs to be verified before `is_substring` can rely on its correctness.
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
    if sub.len() == 0 {
        // An empty string is always a substring of any string (including an empty string).
        // vacuous case for substring, it's always a prefix and therefore a substring
        // is_substring_pred("", S) is true because for i=0, is_prefix_pred("", S.len()) works
        // is_prefix_pred("", X) is true for any X
        assert(is_substring_pred(sub, str));
        return true;
    }

    if sub.len() > str.len() {
        // If sub is longer than str, it cannot be a substring.
        // is_substring_pred(sub, str) would be false since sub.len() <= (str.len() - i) would fail
        assert(is_not_substring_pred(sub, str));
        return false;
    }

    let search_limit: nat = (str.len() - sub.len());
    let mut i: nat = 0;
    let mut found: bool = false;

    // We can prove that if sub is a substring, it must be found within the first (str.len() - sub.len() + 1) positions.
    // if is_substring_at_pred(sub, str, i), then sub.len() > 0 and i + sub.len() <= str.len().
    // So i <= str.len() - sub.len().
    // If sub.len() == 0, then we already handled it. If sub.len() > 0, then i_max = str.len() - sub.len().

    proof {
        lemma_is_substring_iff_exists_is_substring_at(sub, str);
        lemma_is_not_substring_iff_forall_not_is_substring_at(sub, str);
    }

    while i <= search_limit && !found
        invariant
            0 <= i <= search_limit + 1,
            // If `found` is true, then `sub` is indeed a substring at index `k < i`.
            found ==> (exists|k: int| 0 <= k && (k as nat) < i && is_substring_at_pred(sub, str, k)),
            // If `found` is false, then `sub` is not a substring at any index up to `i-1`.
            !found ==> (forall|k: int| 0 <= k && (k as nat) < i ==> !is_substring_at_pred(sub, str, k)),
    {
        // Use ghost variables for subrange arguments
        let ghost current_sub_start = i;
        let ghost current_sub_end = i + sub.len();

        let current_sub = str.subrange(current_sub_start as int, current_sub_end as int);

        // We check if `current_sub` (which has length `sub.len()`) is equal to `sub`.
        // This is equivalent to `is_substring_at_pred(sub, str, i)`.
        let check_res = is_prefix(sub, current_sub); // is_prefix_pred(sub, current_sub)

        if check_res {
            found = true;
            proof {
                assert(is_prefix_pred(sub, current_sub));
                // since sub.len() == current_sub.len(), is_prefix_pred implies equality
                assert(sub.len() <= current_sub.len());
                assert(sub == current_sub.subrange(0, sub.len() as int));
                assert(sub == current_sub); // because sub.len() == current_sub.len()
                assert(current_sub == str.subrange(i as int, (i + sub.len()) as int));
                assert(is_substring_at_pred(sub, str, i as int));
            }
        } else {
            proof {
                assert(!is_prefix_pred(sub, current_sub)); // By lemma_is_prefix_equiv
                // Since current_sub.len() == sub.len(), !is_prefix_pred(sub, current_sub) means current_sub != sub
                assert(is_not_prefix_pred(sub, current_sub));
                assert(!(sub.len() <= current_sub.len() && sub == current_sub.subrange(0, sub.len() as int)));
                assert(!is_substring_at_pred(sub, str, i as int));
            }
        }
        i = i + 1;
    }

    if found {
        proof {
            // If `found` is true, then by the loop invariant, we found a `k < i` such that `is_substring_at_pred(sub, str, k)`.
            // This immediately implies `is_substring_pred(sub, str)`.
            assert(is_substring_pred(sub, str)); // By lemma_is_substring_iff_exists_is_substring_at
        }
        true
    } else {
        proof {
            // If `found` is false, then by the loop invariant, for all `k < i`, `!is_substring_at_pred(sub, str, k)`.
            // Since `i` reached `search_limit + 1`, this means for all `k` from `0` to `search_limit`, `!is_substring_at_pred(sub, str, k)`.
            // Which means `!is_substring_pred(sub, str)`.
            assert(i == search_limit + 1);
            assert forall|k: int| 0 <= k && (k as nat) <= search_limit implies !is_substring_at_pred(sub, str, k) by {
                assert((k as nat) < i); // from loop invariant
                assert(!is_substring_at_pred(sub, str, k));
            }
            assert(is_not_substring_pred(sub, str)); // By lemma_is_not_substring_iff_forall_not_is_substring_at
        }
        false
    }
}
// </vc-code>

fn main() {}

}