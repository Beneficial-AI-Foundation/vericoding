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
proof fn add_nonneg(a: int, b: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        a + b >= 0,
{
    proof {
        assert(a + b >= 0);
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
    let n_int = n as int;
    let h1s = h1@.map_values(|x: i8| x as int);
    let h2s = h2@.map_values(|x: i8| x as int);

    let mut i: int = 1;
    let mut curr1: int = h1s@[0];
    let mut curr2: int = h2s@[0];

    proof {
        assert(curr1 == max_height_ending_in_row1(1, h1s, h2s));
        assert(curr2 == max_height_ending_in_row2(1, h1s, h2s));
    }

    while i < n_int
        invariant
            1 <= i <= n_int,
            curr1 == max_height_ending_in_row1(i, h1s, h2s),
            curr2 == max_height_ending_in_row2(i, h1s, h2s),
        decreases n_int - i
    {
        let idx = i;
        let next1_from_row2 = curr2 + h1s@[idx];
        let next1 = if next1_from_row2 > curr1 { next1_from_row2 } else { curr1 };
        let next2_from_row1 = curr1 + h2s@[idx];
        let next2 = if next2_from_row1 > curr2 { next2_from_row1 } else { curr2 };

        i = i + 1;
        curr1 = next1;
        curr2 = next2;

        proof {
            assert(curr1 == max_height_ending_in_row1(i, h1s, h2s));
            assert(curr2 == max_height_ending_in_row2(i, h1s, h2s));
        }
    }

    if curr1 > curr2 { curr1 as i8 } else { curr2 as i8 }
}

// </vc-code>


}

fn main() {}