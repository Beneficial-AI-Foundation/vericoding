// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn abs_diff(x: int, y: int) -> int {
    if x >= y { x - y } else { y - x }
}

spec fn count_valid_pairs(sequence: Seq<i32>, k: int, start: int) -> nat
    decreases sequence.len() - start
{
    if start >= sequence.len() {
        0
    } else {
        let count_with_current = count_pairs_from_index(sequence, k, start, start + 1);
        count_with_current + count_valid_pairs(sequence, k, start + 1)
    }
}

spec fn count_pairs_from_index(sequence: Seq<i32>, k: int, i: int, j: int) -> nat
    decreases sequence.len() - j
{
    if j >= sequence.len() {
        0nat
    } else {
        let has_variation: nat = if abs_diff(sequence[i] as int, sequence[j] as int) >= k { 1nat } else { 0nat };
        has_variation + count_pairs_from_index(sequence, k, i, j + 1)
    }
}

fn total_variation_count(n: usize, k: i32, sequence: Vec<i32>) -> (result: usize)
    requires 
        sequence.len() == n,
        n > 0,
        k >= 0,
    ensures 
        result >= 0,
        result <= (n * (n - 1)) / 2,
        result == count_valid_pairs(sequence@, k as int, 0),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

}
fn main() {}