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
/* helper modified by LLM (iteration 4): Added lemmas to help prove non-negativity and bounds */
proof fn lemma_max_height_nonnegative(n: int, h1: Seq<int>, h2: Seq<int>)
    requires valid_input(n, h1, h2)
    ensures 
        max_height_ending_in_row1(n, h1, h2) >= 0,
        max_height_ending_in_row2(n, h1, h2) >= 0
    decreases n
{
    if n == 1 {
        assert(h1[0] >= 0);
        assert(h2[0] >= 0);
    } else {
        lemma_max_height_nonnegative(n - 1, h1, h2);
        assert(max_height_ending_in_row1(n - 1, h1, h2) >= 0);
        assert(max_height_ending_in_row2(n - 1, h1, h2) >= 0);
        assert(h1[n - 1] >= 0);
        assert(h2[n - 1] >= 0);
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
    /* code modified by LLM (iteration 4): Fixed initial dp values to ensure non-negativity and added overflow checks */
    assert(h1@[0] >= 0);
    assert(h2@[0] >= 0);
    
    let mut dp1: i8 = h1[0];
    let mut dp2: i8 = h2[0];
    
    proof {
        lemma_max_height_nonnegative(1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int));
    }
    
    let mut i: usize = 1;
    while i < n as usize
        invariant
            1 <= i <= n as usize,
            n >= 1,
            h1.len() >= n as usize,
            h2.len() >= n as usize,
            dp1 >= 0,
            dp2 >= 0,
            dp1 as int == max_height_ending_in_row1(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
            dp2 as int == max_height_ending_in_row2(i as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
            valid_input(n as int, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int)),
        decreases (n as usize) - i
    {
        let prev_dp1 = dp1;
        let prev_dp2 = dp2;
        
        proof {
            lemma_max_height_nonnegative(i as int + 1, h1@.map_values(|x: i8| x as int), h2@.map_values(|x: i8| x as int));
        }
        
        assert(prev_dp2 as int + h1@[i as int] as int <= i8::MAX as int);
        let take_from_row2 = prev_dp2 + h1[i];
        dp1 = if take_from_row2 > prev_dp1 { take_from_row2 } else { prev_dp1 };
        
        assert(prev_dp1 as int + h2@[i as int] as int <= i8::MAX as int);
        let take_from_row1 = prev_dp1 + h2[i];
        dp2 = if take_from_row1 > prev_dp2 { take_from_row1 } else { prev_dp2 };
        
        i = i + 1;
    }
    
    if dp1 > dp2 { dp1 } else { dp2 }
}
// </vc-code>


}

fn main() {}