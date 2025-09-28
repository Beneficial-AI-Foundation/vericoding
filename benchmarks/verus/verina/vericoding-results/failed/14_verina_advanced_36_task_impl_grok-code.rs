// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_matches(xs: Seq<u64>, x: u64) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let first_match: nat = if xs[0] == x { 1 } else { 0 };
        first_match + count_matches(xs.skip(1), x)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires 
        xs.len() > 0,
        exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
    ensures
        count_matches(xs@, result) > xs.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Initialized candidate to xs[0] and count to 1, starting loop from i=1 */
    let mut candidate = xs[0];
    let mut count = 1;
    let length = xs.len();
    let mut i = 1;
    while i < length
        invariant
            0 <= i <= length,
    {
        if count == 0 {
            candidate = xs[i];
            count = 1;
        } else if xs[i] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
        i += 1;
    }
    // Verification phase: count occurrences of candidate
    let mut total_count = 0;
    let mut j = 0;
    while j < length
        invariant
            0 <= j <= length,
            0 <= total_count <= j,
    {
        if xs[j] == candidate {
            total_count += 1;
        }
        j += 1;
    }
    proof {
        assert(total_count > length / 2);
    }
    candidate
}
// </vc-code>

}
fn main() {}