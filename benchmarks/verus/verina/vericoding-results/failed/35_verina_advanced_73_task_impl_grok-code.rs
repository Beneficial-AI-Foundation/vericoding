// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed compilation errors by using nat types for indices and expected value, removing invalid 'nat' suffixes on literals, and ensuring proper type matching for indexing and comparisons */
    let mut expected: nat = 0;
    let mut i: nat = 0;
    while i < l.len()
        invariant
            forall|k: nat| k < expected ==> exists|j: nat| 0 <= j < l.len() && l[j] == k,
            i <= l.len()
        decreases l.len() - i
    {
        if l[i] > expected {
            return expected;
        } else if l[i] == expected {
            expected = expected + 1;
        }
        i = i + 1;
    }
    expected
}
// </vc-code>

}
fn main() {}