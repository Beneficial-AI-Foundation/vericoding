use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
fn abs_diff(a: i64, b: i64) -> (res: i64)
    ensures res == abs(a - b)
{
    if a >= b {
        a - b
    } else {
        b - a
    }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();

    // Loop invariants for the outer loop
    // - `i` iterates from 0 to n - 1
    // - For any `i_prev` < `i`, and any `j_prev` such that `i_prev` < `j_prev` < n,
    //   it is not the case that `abs(numbers[i_prev] - numbers[j_prev]) < threshold`.
    //   This means we haven't found any close elements yet in previous iterations.
    for i in 0..n
        invariant
            0 <= i <= n,
            !exists|i_prev: int, j_prev: int| 0 <= i_prev < i <= j_prev < n && abs(numbers[i_prev] - numbers[j_prev]) < threshold,
            !exists|i_prev: int, j_prev: int| 0 <= i_prev < j_prev < i && abs(numbers[i_prev] - numbers[j_prev]) < threshold,
    {
        // Loop invariants for the inner loop
        // - `j` iterates from `i + 1` to `n`
        // - For the current `i`, and any `j_prev` such that `i < j_prev < j`,
        //   it is not the case that `abs(numbers[i] - numbers[j_prev]) < threshold`.
        //   This means we haven't found any close elements with the current `i` yet.
        for j in (i + 1)..n
            invariant
                0 <= i < j <= n,
                !exists|j_prev: int| (i as int) < j_prev < (j as int) && abs(numbers[i as int] - numbers[j_prev]) < threshold,
                // Combine with outer loop invariant
                !exists|i_prev: int, j_prev: int| 0 <= i_prev < i <= j_prev < n && abs(numbers[i_prev] - numbers[j_prev]) < threshold,
                !exists|i_prev: int, j_prev: int| 0 <= i_prev < j_prev < i && abs(numbers[i_prev] - numbers[j_prev]) < threshold,
        {
            let diff = abs_diff(numbers[i], numbers[j]);
            if diff < threshold {
                return true;
            }
        }
    }
    // If we reach here, it means no pair of close elements was found.
    // This proof block shows that if we iterate through all possible pairs (i, j)
    // and `abs(numbers[i] - numbers[j]) < threshold` is never true,
    // then the exists|i, j| condition is false.
    proof {
        assert forall|i: int, j: int|
            0 <= i < j < n implies !(abs(numbers[i] - numbers[j]) < threshold)
            by {
                // This is precisely what the loops establish negation of the postcondition.
                // The loop invariants ensure that if `true` was not returned,
                // then for all `0 <= i < j < n`, `abs(numbers[i] - numbers[j]) >= threshold`.
                // The final overall invariant of the outer loop after it finishes is:
                // !exists|i_prev: int, j_prev: int| 0 <= i_prev < n <= j_prev < n && abs(numbers[i_prev] - numbers[j_prev]) < threshold && i_prev != j_prev,
                // which simplifies to:
                // !exists|i_prev: int, j_prev: int| 0 <= i_prev < n && i_prev+1 <= j_prev < n && abs(numbers[i_prev] - numbers[j_prev]) < threshold
                // (given j must be greater than i)
            }
    }
    false
}
// </vc-code>

fn main() {}
}