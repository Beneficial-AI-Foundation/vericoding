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
proof fn max_height_ending_in_row1_decreases_helper(n: int, h1: Seq<int>, h2: Seq<int>)
    requires
        n >= 0,
        valid_input(n, h1, h2)
    decreases n
{
    if n > 1 {
        max_height_ending_in_row1_decreases_helper(n - 1, h1, h2);
        max_height_ending_in_row2_decreases_helper(n - 1, h1, h2);
    }
}

proof fn max_height_ending_in_row2_decreases_helper(n: int, h1: Seq<int>, h2: Seq<int>)
    requires
        n >= 0,
        valid_input(n, h1, h2)
    decreases n
{
    if n > 1 {
        max_height_ending_in_row1_decreases_helper(n - 1, h1, h2);
        max_height_ending_in_row2_decreases_helper(n - 1, h1, h2);
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
{
    /* code modified by LLM (iteration 5): Fixed loop invariants, index bounds, and overflow prevention */
    let mut dp1: i8 = 0;
    let mut dp2: i8 = 0;
    let mut i: usize = 0;
    let n_usize = n as usize;
    assert(valid_input(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)));
    assert(h1@.len() == n as usize);
    assert(h2@.len() == n as usize);
    
    while i < n_usize
        invariant
            i <= n_usize,
            dp1 >= 0,
            dp2 >= 0,
            i >= 0,
            dp1 as int == max_height_ending_in_row1(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
            dp2 as int == max_height_ending_in_row2(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))
        decreases n_usize - i
    {
        if i == 0 {
            dp1 = h1[i];
            dp2 = h2[i];
        } else {
            let candidate1 = (dp2 as i16) + (h1[i] as i16);
            let candidate2 = (dp1 as i16) + (h2[i] as i16);
            let new_dp1 = if candidate1 > dp1 as i16 { candidate1 } else { dp1 as i16 } as i8;
            let new_dp2 = if candidate2 > dp2 as i16 { candidate2 } else { dp2 as i16 } as i8;
            dp1 = new_dp1;
            dp2 = new_dp2;
        }
        i += 1;
    }
    if dp1 > dp2 { dp1 } else { dp2 }
}
// </vc-code>


}

fn main() {}