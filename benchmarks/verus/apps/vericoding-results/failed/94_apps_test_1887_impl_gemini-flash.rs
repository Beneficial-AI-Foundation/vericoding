// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, h1: Seq<int>, h2: Seq<int>) -> bool {
    n >= 1 && h1.len() >= n && h2.len() >= n &&
    (forall|i: int| 0 <= i < n ==> h1[i] >= 0) &&
    (forall|i: int| 0 <= i < n ==> h2[i] >= 0)
}

spec fn max_team_height(n: int, h1: Seq<int>, h2: Seq<int>) -> int
    recommends valid_input(n, h1, h2)
{
    let dp1 = max_height_ending_in_row1(n, h1, h2);
    let dp2 = max_height_ending_in_row2(n, h1, h2);
    if dp1 > dp2 { dp1 } else { dp2 }
}

spec fn max_height_ending_in_row1(n: int, h1: Seq<int>, h2: Seq<int>) -> int
    recommends valid_input(n, h1, h2)
    decreases n via max_height_ending_in_row1_decreases
{
    if n == 1 { h1[0] }
    else {
        let prev_row2 = max_height_ending_in_row2(n-1, h1, h2);
        let prev_row1 = max_height_ending_in_row1(n-1, h1, h2);
        let take_from_row2 = prev_row2 + h1[n-1];
        if take_from_row2 > prev_row1 { take_from_row2 } else { prev_row1 }
    }
}

spec fn max_height_ending_in_row2(n: int, h1: Seq<int>, h2: Seq<int>) -> int
    recommends valid_input(n, h1, h2)
    decreases n via max_height_ending_in_row2_decreases
{
    if n == 1 { h2[0] }
    else {
        let prev_row1 = max_height_ending_in_row1(n-1, h1, h2);
        let prev_row2 = max_height_ending_in_row2(n-1, h1, h2);
        let take_from_row1 = prev_row1 + h2[n-1];
        if take_from_row1 > prev_row2 { take_from_row1 } else { prev_row2 }
    }
}

#[via_fn]
proof fn max_height_ending_in_row1_decreases(n: int, h1: Seq<int>, h2: Seq<int>) {
    assume(false);
}

#[via_fn]
proof fn max_height_ending_in_row2_decreases(n: int, h1: Seq<int>, h2: Seq<int>) {
    assume(false);
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, h1: Vec<i8>, h2: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))
    ensures 
        result >= 0,
        result as int == max_team_height(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed arithmetic underflow/overflow and precondition not met for vector indexing by adding checks and proofs for `i - 1`. Corrected casting of `n` to `usize` for vector operations and `int` for spec functions. Ensured correct updates to `dp1` and `dp2` vectors. Added proof for `dp1` and `dp2` lengths to satisfy invariant. Simplified some conditions in the invariant. Added assert to prove that `j+1` is within bounds. */
{
    let n_usize = n as usize;

    let mut dp1: Vec<i8> = Vec::new();
    let mut dp2: Vec<i8> = Vec::new();

    if n_usize == 0 {
        return 0 as i8;
    }

    dp1.push(h1[0]);
    dp2.push(h2[0]);

    let mut i: usize = 1;
    while i < n_usize
        invariant
            1 <= i as int <= n as int,
            dp1.len() == i,
            dp2.len() == i,
            // dp1[k] holds the max height ending in row 1 for (k+1) elements
            (forall|j: int| 0 <= j < i as int ==> dp1@[j] as int == max_height_ending_in_row1(j + 1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))),
            // dp2[k] holds the max height ending in row 2 for (k+1) elements
            (forall|j: int| 0 <= j < i as int ==> dp2@[j] as int == max_height_ending_in_row2(j + 1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)))
        decreases (n_usize - i) as int
    {
        proof {
            assert(i - 1 < dp1.len());
            assert(i - 1 < dp2.len());
            assert((i + 1) as int <= n as int);
        }

        let prev_row2 = dp2[i - 1];
        let prev_row1_dp = dp1[i - 1];

        let take_from_row2 = prev_row2 + h1[i];
        let current_dp1 = if take_from_row2 > prev_row1_dp { take_from_row2 } else { prev_row1_dp };
        dp1.push(current_dp1);

        let prev_row1 = dp1[i - 1];
        let prev_row2_dp = dp2[i - 1];

        let take_from_row1 = prev_row1 + h2[i];
        let current_dp2 = if take_from_row1 > prev_row2_dp { take_from_row1 } else { prev_row2_dp };
        dp2.push(current_dp2);

        proof {
            assert(dp1.len() == i + 1);
            assert(dp2.len() == i + 1);
            assert(current_dp1 as int == max_height_ending_in_row1((i + 1) as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
            assert(current_dp2 as int == max_height_ending_in_row2((i + 1) as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
        }

        i = i + 1;
    }

    let final_dp1 = dp1[n_usize - 1];
    let final_dp2 = dp2[n_usize - 1];

    proof {
        assert(final_dp1 as int == max_height_ending_in_row1(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
        assert(final_dp2 as int == max_height_ending_in_row2(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
    }

    if final_dp1 > final_dp2 {
        final_dp1
    } else {
        final_dp2
    }
}
// </vc-code>


}

fn main() {}