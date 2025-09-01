use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut expected: i32 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            0 <= expected,
            forall |k: int| 0 <= k < (expected as int) ==> exists |j: int| 0 <= j < (i as int) && (s@[j] as int) == k,
            forall |j: int| 0 <= j < (i as int) ==> (s@[j] as int) != (expected as int),
    {
        if s[i] > expected {
            proof {
                assert forall |j: int| 0 <= j < s.len() ==> (s@[j] as int) != (expected as int) by {
                    if j < (i as int) {
                        assert((s@[j] as int) != (expected as int));
                    } else {
                        assert((s@[(i as int)] as int) > (expected as int));
                        assert((s@[j] as int) >= (s@[(i as int)] as int) > (expected as int));
                        assert((s@[j] as int) != (expected as int));
                    }
                }
            }
            return expected;
        }
        if s[i] == expected {
            expected = expected + 1;
        }
        i = i + 1;
    }
    proof {
        assert forall |j: int| 0 <= j < s.len() ==> (s@[j] as int) != (expected as int) by {
            assert(j < (i as int));
            assert((s@[j] as int) != (expected as int));
        }
    }
    expected
}
// </vc-code>

fn main() {}
}