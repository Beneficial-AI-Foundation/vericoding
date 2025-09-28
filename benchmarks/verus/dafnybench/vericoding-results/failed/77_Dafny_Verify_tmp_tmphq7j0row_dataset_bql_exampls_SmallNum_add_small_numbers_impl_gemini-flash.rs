use vstd::prelude::*;

verus! {

// <vc-helpers>
fn add_with_max(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
        max >= 0,
    ensures
        r <= (max as int) * (n as int),
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;

    proof {
        assert(0 <= sum as int) by (nonlinear_arith);
    }

    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            sum as int <= (max as int) * (i as int),
            forall|j: int| 0 <= j && j < n ==> a[j] <= max,
            max >= 0,
            0 <= sum as int, // Added: sum must be non-negative
        decreases n - i
    {
        let val = a[i];

        proof {
            assert(0 <= i && i < n); // Prove index is in bounds
            assert(val <= max); // From invariant
            assert(val as int >= 0) by (nonlinear_arith); // Values in array are non-negative, implied by sum being non-negative
            assert(a[i] as int <= max as int) by (nonlinear_arith);
        }

        let old_sum = sum;

        sum = sum + val;

        proof {
            assert((old_sum as int) <= (max as int) * (i as int));
            assert((val as int) <= (max as int));
            assert((old_sum as int) + (val as int) <= (max as int) * (i as int) + (max as int)) by (nonlinear_arith);
            assert((old_sum as int) + (val as int) <= (max as int) * ((i + 1) as int)) by (nonlinear_arith);

            // Added proof that sum remains non-negative
            assert(old_sum as int >= 0);
            assert(val as int >= 0); // Assuming val is non-negative
            assert(sum as int >= 0) by (nonlinear_arith); // sum is non-negative since old_sum and val are non-negative

            assert(sum as int == (old_sum as int) + (val as int));
            assert(sum as int <= (max as int) * ((i + 1) as int));
        }

        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// <vc-code>
{
    add_with_max(a, n, max)
}
// </vc-code>

fn main() {
}

}