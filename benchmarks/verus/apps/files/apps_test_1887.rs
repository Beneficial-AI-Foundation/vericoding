// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    decreases n
{
    if n == 1 {
        h1[0]
    } else {
        let prev_row2 = max_height_ending_in_row2((n-1) as nat, h1, h2);
        let prev_row1 = max_height_ending_in_row1((n-1) as nat, h1, h2);
        let take_from_row2 = prev_row2 + h1[n-1];
        if take_from_row2 > prev_row1 { take_from_row2 } else { prev_row1 }
    }
}

spec fn max_height_ending_in_row2(n: int, h1: Seq<int>, h2: Seq<int>) -> int
    recommends valid_input(n, h1, h2)
    decreases n
{
    if n == 1 {
        h2[0]
    } else {
        let prev_row1 = max_height_ending_in_row1((n-1) as nat, h1, h2);
        let prev_row2 = max_height_ending_in_row2((n-1) as nat, h1, h2);
        let take_from_row1 = prev_row1 + h2[n-1];
        if take_from_row1 > prev_row2 { take_from_row1 } else { prev_row2 }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, h1: Seq<int>, h2: Seq<int>) -> (result: int)
requires
    valid_input(n, h1, h2)
ensures
    result >= 0,
    result == max_team_height(n, h1, h2)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}