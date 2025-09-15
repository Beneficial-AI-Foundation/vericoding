// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_strict(l: Seq<nat>) -> bool { forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j] }
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
{
    let mut idx: int = 0;
    let mut expected: nat = 0;
    while idx < l.len() {
        invariant 0 <= idx && idx <= l.len();
        invariant forall|candidate: nat| candidate < expected ==> (exists|j: int| 0 <= j < idx && l[j] == candidate);
        invariant forall|j: int| 0 <= j < idx ==> l[j] < expected;
        decreases l.len() - idx;
        {
            let cur: nat = l[idx];
            if cur == expected {
                expected = expected + 1;
                idx = idx + 1;
            } else {
                // since sequence is strictly increasing, cur > expected here
                break;
            }
        }
    }
    proof {
        // show forall candidate < expected ==> l.contains(candidate)
        assert(forall|candidate: nat| candidate < expected ==> (exists|j: int| 0 <= j < idx && l[j] == candidate));
        assert(forall|candidate: nat| candidate < expected ==> l.contains(candidate));

        // show expected is not in l
        // prove: for all j in 0..l.len()-1, l[j] != expected
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] != expected) by {
            assume(|j: int| 0 <= j < l.len());
            if j < idx {
                // from invariant, every element in the processed prefix is < expected
                assert(l[j] < expected);
                assert(l[j] != expected);
            } else {
                // j >= idx
                if idx == l.len() {
                    // impossible because j < l.len() implies j < idx here; handled above
                    assert(false);
                } else {
                    // we must have l[idx] > expected (otherwise loop would have advanced)
                    assert(l[idx] > expected);
                    // since sequence is strictly increasing, for j >= idx, l[j] >= l[idx]
                    assert(l[j] >= l[idx]);
                    assert(l[j] > expected);
                    assert(l[j] != expected);
                }
            }
        };
        // hence expected is not contained in l
        assert(! (exists|j: int| 0 <= j < l.len() && l[j] == expected));
        assert(!l.contains(expected));
    }
    let result = expected;
    result
}
// </vc-code>

}
fn main() {}