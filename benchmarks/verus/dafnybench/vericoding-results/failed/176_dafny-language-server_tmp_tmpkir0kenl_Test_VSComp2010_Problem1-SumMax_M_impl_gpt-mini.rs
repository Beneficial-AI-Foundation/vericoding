use vstd::prelude::*;

verus! {

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
fn lemma_mul_lt_pos(k: int, x: int, y: int)
    requires
        k > 0,
        x < y,
    ensures
        k * x < k * y,
{
    // trivial by multiplication monotonicity
    assert(k * x < k * y);
}
// </vc-helpers>

// <vc-spec>
fn M(N: int, a: &[int]) -> (result: (int, int))
    requires 
        0 <= N,
        a.len() == N,
        forall|k: int| 0 <= k && k < N ==> 0 <= a[k],
    ensures 
        result.0 <= N * result.1;
// </vc-spec>
// <vc-code>
{
    let mut sum: int = 0;
    let mut max: int = 0;
    let mut i: int = 0;
    while i < N
        invariant 0 <= i && i <= N;
        invariant sum >= 0;
        invariant max >= 0;
        invariant sum <= i * max;
        decreases N - i;
    {
        let old_i = i;
        let old_sum = sum;
        let old_max = max;
        let ai = a[old_i];
        // update new values
        let new_sum = old_sum + ai;
        let new_max = if ai > old_max { ai } else { old_max };
        sum = new_sum;
        max = new_max;
        i = old_i + 1;
        proof {
            // From loop invariant at start: old_sum <= old_i * old_max
            assert(old_sum <= old_i * old_max);
            if ai <= old_max {
                // new_max = old_max, new_sum = old_sum + ai <= old_sum + old_max
                assert(ai <= old_max);
                assert(new_sum <= old_sum + old_max);
                assert(old_sum + old_max <= old_i * old_max + old_max);
                assert(old_sum + old_max <= (old_i + 1) * old_max);
                assert(new_sum <= (old_i + 1) * old_max);
                assert(new_sum <= i * max);
            } else {
                // ai > old_max, so new_max = ai
                assert(old_max < ai);
                if old_i == 0 {
                    // when old_i == 0, old_sum <= 0 and old_sum >= 0 imply old_sum == 0
                    assert(old_sum >= 0);
                    assert(old_sum <= 0);
                    assert(old_sum == 0);
                    assert(new_sum == ai);
                    assert(new_sum <= (old_i + 1) * ai);
                    assert(new_sum <= i * max);
                } else {
                    // old_i > 0: from old_sum <= old_i*old_max and old_max < ai,
                    // multiply gives old_i*old_max < old_i*ai, so old_sum < old_i*ai => old_sum <= old_i*ai
                    assert(old_i > 0);
                    lemma_mul_lt_pos(old_i, old_max, ai);
                    assert(old_i * old_max < old_i * ai);
                    assert(old_sum <= old_i * old_max);
                    assert(old_sum < old_i * ai);
                    assert(old_sum <= old_i * ai);
                    assert(new_sum <= old_i * ai + ai);
                    assert(new_sum <= (old_i + 1) * ai);
                    assert(new_sum <= i * max);
                }
            }
            // maintain non-negativity invariants
            assert(sum >= 0);
            assert(max >= 0);
        }
    }
    (sum, max)
}
// </vc-code>

fn main() {}

}