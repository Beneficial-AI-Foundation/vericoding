// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_power_of_two(n: int) -> bool
    decreases n
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else if n % 2 == 1 {
        false
    } else {
        is_power_of_two(n / 2)
    }
}

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn correct_result(n: int, result: int) -> bool {
    if n % 2 == 1 {
        result == (n - 1) / 2
    } else {
        exists|z: int| 1 <= z <= n && is_power_of_two(z) && z <= n && z * 2 > n && result == (n - z) / 2
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [fix compilation error by revealing spec func] */
proof fn lemma_power_of_two_gt_one_is_even(n: int)
    requires
        is_power_of_two(n),
        n > 1,
    ensures
        n % 2 == 0,
{
    reveal(is_power_of_two);
}

/* helper modified by LLM (iteration 3): [fix compilation error by revealing spec func] */
proof fn lemma_is_power_of_two_times_two(n: int)
    requires
        is_power_of_two(n),
        n >= 1,
    ensures
        is_power_of_two(n * 2),
{
    reveal(is_power_of_two);
}

/* helper modified by LLM (iteration 5): [add invariant and adjust decreases] */
fn find_largest_power_of_two_le(n: i8) -> (z: i8)
    requires
        n >= 1,
    ensures
        is_power_of_two(z as int),
        z as int <= n as int,
        (z as int) * 2 > n as int,
        1 <= z,
{
    let mut z: i16 = 1;
    let n_i16 = n as i16;
    while z * 2 <= n_i16
        invariant
            is_power_of_two(z as int),
            z <= n_i16,
            1 <= z,
            n_i16 <= 127,
        decreases (n_i16 as int) - (z as int),
    {
        proof {
            lemma_is_power_of_two_times_two(z as int);
        }
        z = z * 2;
    }
    z as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures correct_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [no change, helper fix is sufficient] */
    if n % 2 == 1 {
        (n - 1) / 2
    } else {
        let z = find_largest_power_of_two_le(n);
        let result = (n - z) / 2;
        proof {
            let ghost n_int = n as int;
            let ghost z_int = z as int;
            assert(n_int % 2 == 0);
            assert(n_int >= 1);
            assert(n_int >= 2);

            if z_int == 1 {
                assert(1 * 2 > n_int);
                assert(n_int < 2);
                assert(false);
            }
            assert(z_int > 1);
            
            lemma_power_of_two_gt_one_is_even(z_int);
            assert(z_int % 2 == 0);

            assert((n_int - z_int) % 2 == 0);
        }
        result
    }
}
// </vc-code>


}

fn main() {}