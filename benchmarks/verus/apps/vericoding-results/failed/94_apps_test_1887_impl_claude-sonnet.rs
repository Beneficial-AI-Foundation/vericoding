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
/* helper modified by LLM (iteration 5): added decreases clause to fix recursive function error */
proof fn max_ending_properties(n: int, h1: Seq<int>, h2: Seq<int>)
    requires valid_input(n, h1, h2)
    ensures
        max_height_ending_in_row1(n, h1, h2) >= 0,
        max_height_ending_in_row2(n, h1, h2) >= 0
    decreases n
{
    if n == 1 {
        assert(max_height_ending_in_row1(n, h1, h2) == h1[0]);
        assert(max_height_ending_in_row2(n, h1, h2) == h2[0]);
    } else {
        max_ending_properties(n-1, h1, h2);
    }
}

proof fn max_team_height_properties(n: int, h1: Seq<int>, h2: Seq<int>)
    requires valid_input(n, h1, h2)
    ensures max_team_height(n, h1, h2) >= 0
{
    max_ending_properties(n, h1, h2);
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
    /* code modified by LLM (iteration 5): added decreases clause to fix loop verification error */
    let mut dp1 = h1[0];
    let mut dp2 = h2[0];
    let mut i = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            dp1 >= 0,
            dp2 >= 0,
            dp1 == max_height_ending_in_row1(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
            dp2 == max_height_ending_in_row2(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int))
        decreases n - i
    {
        let new_dp1 = if dp2 + h1[i as usize] > dp1 { dp2 + h1[i as usize] } else { dp1 };
        let new_dp2 = if dp1 + h2[i as usize] > dp2 { dp1 + h2[i as usize] } else { dp2 };
        
        dp1 = new_dp1;
        dp2 = new_dp2;
        i += 1;
    }
    
    let result = if dp1 > dp2 { dp1 } else { dp2 };
    
    proof {
        max_team_height_properties(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}