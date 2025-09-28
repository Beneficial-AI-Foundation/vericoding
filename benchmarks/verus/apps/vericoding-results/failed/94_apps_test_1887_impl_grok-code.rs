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
/* helper modified by LLM (iteration 2): implementing decreases proofs for spec functions */

#[via_fn]
proof fn max_height_ending_in_row1_decreases(n: int, h1: Seq<int>, h2: Seq<int>) {
    if n > 1 {
        reveal(max_height_ending_in_row1);
        reveal(max_height_ending_in_row2);
        assert(max_height_ending_in_row1(n, h1, h2) == {
            let prev_row2 = max_height_ending_in_row2(n-1, h1, h2);
            let prev_row1 = max_height_ending_in_row1(n-1, h1, h2);
            let take_from_row2 = prev_row2 + h1[n-1];
            if take_from_row2 > prev_row1 { take_from_row2 } else { prev_row1 }
        });
        max_height_ending_in_row1_decreases(n-1, h1, h2);
        max_height_ending_in_row2_decreases(n-1, h1, h2);
    }
}

#[via_fn]
proof fn max_height_ending_in_row2_decreases(n: int, h1: Seq<int>, h2: Seq<int>) {
    if n > 1 {
        reveal(max_height_ending_in_row2);
        reveal(max_height_ending_in_row1);
        assert(max_height_ending_in_row2(n, h1, h2) == {
            let prev_row1 = max_height_ending_in_row1(n-1, h1, h2);
            let prev_row2 = max_height_ending_in_row2(n-1, h1, h2);
            let take_from_row1 = prev_row1 + h2[n-1];
            if take_from_row1 > prev_row2 { take_from_row1 } else { prev_row2 }
        });
        max_height_ending_in_row1_decreases(n-1, h1, h2);
        max_height_ending_in_row2_decreases(n-1, h1, h2);
    }
}
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
/* code modified by LLM (iteration 2): implementing dynamic programming for max team height */
{
    let dp1 = vec![h1[0]];
    let dp2 = vec![h2[0]];
    proof {
        reveal(max_height_ending_in_row1);
        reveal(max_height_ending_in_row2);
        assert(dp1@[0] as int == max_height_ending_in_row1(1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
        assert(dp2@[0] as int == max_height_ending_in_row2(1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
    }
    for i in 1..n as usize
        invariant
            0 <= i <= n as usize,
            dp1@.len() == i + 1,
            dp2@.len() == i + 1,
            forall |k: int| 0 <= k <= i ==> dp1@[k] as int == max_height_ending_in_row1(k + 1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
            forall |k: int| 0 <= k <= i ==> dp2@[k] as int == max_height_ending_in_row2(k + 1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))
        decreases
            n as usize - i
    {
        let take_from_row2 = dp2[i-1] + h1[i];
        let prev = dp1[i-1];
        let new_dp1 = if take_from_row2 > prev { take_from_row2 } else { prev };
        dp1.push(new_dp1);
        let take_from_row1 = dp1[i-1] + h2[i];
        let prev = dp2[i-1];
        let new_dp2 = if take_from_row1 > prev { take_from_row1 } else { prev };
        dp2.push(new_dp2);
        proof {
            reveal(max_height_ending_in_row1);
            reveal(max_height_ending_in_row2);
            let prev_row2 = dp2@[i-1] as int;
            let prev_row1 = dp1@[i-1] as int;
            let take_from_row2_val = prev_row2 + h1@[i as int] as int;
            assert(new_dp1 as int == if take_from_row2_val > prev_row1 { take_from_row2_val } else { prev_row1 });
            let take_from_row1_val = dp1@[i-1] as int + h2@[i as int] as int;
            let prev_row2_for_row2 = dp2@[i-1] as int;
            assert(new_dp2 as int == if take_from_row1_val > prev_row2_for_row2 { take_from_row1_val } else { prev_row2_for_row2 });
        }
    }
    let result = if dp1[(n as usize)-1] > dp2[(n as usize)-1] { dp1[(n as usize)-1] } else { dp2[(n as usize)-1] };
    return result;
}
// </vc-code>


}

fn main() {}