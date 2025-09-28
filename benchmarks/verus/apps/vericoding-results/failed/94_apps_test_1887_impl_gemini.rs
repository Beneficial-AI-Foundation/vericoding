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
/* helper modified by LLM (iteration 4): [removed duplicate function definitions] */
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
{
    /* code modified by LLM (iteration 4): [fix compilation errors due to ghost types in exec code] */
    ghost let n_int = n as int;
    ghost let sh1 = h1@.map_values(|x: i8| x as int);
    ghost let sh2 = h2@.map_values(|x: i8| x as int);

    if n == 1i8 {
        let res1 = h1[0];
        let res2 = h2[0];
        let max_val = if res1 > res2 { res1 } else { res2 };
        return max_val;
    }

    let mut dp1: i64 = h1[0] as i64;
    let mut dp2: i64 = h2[0] as i64;

    let mut i: i8 = 1;
    while i < n
        invariant
            n > 1,
            1 <= i < n,
            valid_input(n_int, sh1, sh2),
            dp1 as int == max_height_ending_in_row1(i as int, sh1, sh2),
            dp2 as int == max_height_ending_in_row2(i as int, sh1, sh2),
        decreases n - i
    {
        let prev_dp1 = dp1;
        let prev_dp2 = dp2;

        let h1_i = h1[i as usize] as i64;
        let h2_i = h2[i as usize] as i64;

        let new_dp1_candidate = prev_dp2 + h1_i;
        dp1 = if new_dp1_candidate > prev_dp1 { new_dp1_candidate } else { prev_dp1 };

        let new_dp2_candidate = prev_dp1 + h2_i;
        dp2 = if new_dp2_candidate > prev_dp2 { new_dp2_candidate } else { prev_dp2 };
        
        i = i + 1;
    }

    let result_val = if dp1 > dp2 { dp1 } else { dp2 };
    
    proof {
        assert(dp1 as int == max_height_ending_in_row1(n_int, sh1, sh2));
        assert(dp2 as int == max_height_ending_in_row2(n_int, sh1, sh2));
        assert(result_val as int == max_team_height(n_int, sh1, sh2));
    }

    result_val as i8
}
// </vc-code>


}

fn main() {}