use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
spec fn contains_internal(v: i32, a_sub: Seq<i32>) -> bool {
    exists|j: int| 0 <= j < a_sub.len() && a_sub[j] == v
}

spec fn upper_bound_internal(v: i32, a_sub: Seq<i32>) -> bool {
    forall|j: int| 0 <= j < a_sub.len() ==> a_sub[j] <= v
}

spec fn is_max_internal(m: i32, a_sub: Seq<i32>) -> bool {
    contains_internal(m, a_sub) && upper_bound_internal(m, a_sub)
}

// Added to fix compilation errors due to missing `subsequence` method
// This helper is not strictly related to the original function logic,
// but required due to how `Seq` and methods are handled in Verus.
// It will allow `a@.subsequence` to be recognized.
proof fn lemma_subsequence(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.subsequence(start, end).len() == end - start,
{
    // No-op, just to make subsequence available for use in specs
    // This function can be empty as its purpose is to introduce the method for verification to pass
}
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut ma: i32 = a[0];
    let mut i: usize = 1;

    proof {
        assert(is_max_internal(ma, a@.subsequence(0, 1)));
    }

    while i < n
        invariant
            0 < i <= n,
            is_max_internal(ma, a@.subsequence(0, i as int)),
    {
        if a[i] > ma {
            ma = a[i];
            proof {
                assert(is_max_internal(ma, a@.subsequence(0, (i + 1) as int)));
            }
        } else {
            proof {
                // To prove is_max_internal(ma, a@.subsequence(0, (i + 1) as int)),
                // we need to show both contain_internal and upper_bound_internal for the new range.

                // Containment:
                // Since ma was is_max_internal(ma, a@.subsequence(0, i as int)),
                // we know ma is contained in a@.subsequence(0, i as int).
                // Thus, ma is also contained in a@.subsequence(0, (i + 1) as int).
                assert(contains_internal(ma, a@.subsequence(0, i as int))); // from invariant
                assert(contains_internal(m: ma, a_sub: a@.subsequence(0, i as int)));
                assert forall |j: int| 0 <= j < i as int implies #[trigger] (a@[j]) <= ma by {
                    assert(upper_bound_internal(ma, a@.subsequence(0, i as int)));
                }

                assert(contains_internal(ma, a@.subsequence(0, (i + 1) as int)));

                // Upper bound:
                // We know from invariant that ma is an upper bound for a@.subsequence(0, i as int).
                // And from the `else` branch condition, we know a[i] <= ma.
                // So, for any j in [0, i+1), either j < i (where a[j] <= ma) or j == i (where a[i] <= ma).
                // Thus, ma is an upper bound for a@.subsequence(0, (i + 1) as int).
                assert(upper_bound_internal(ma, a@.subsequence(0, i as int))); // from invariant
                assert(a[i] <= ma); // from else branch condition

                assert(upper_bound_internal(ma, a@.subsequence(0, (i + 1) as int)));
                assert(is_max_internal(ma, a@.subsequence(0, (i + 1) as int)));
            }
        }
        i = i + 1;
    }
    ma
}
// </vc-code>

fn main() {}

}