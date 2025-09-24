// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(coins: Seq<int>) -> bool {
    coins.len() == 5 && forall|i: int| 0 <= i < coins.len() ==> #[trigger] coins[i] >= 0 && #[trigger] coins[i] <= 100
}

spec fn total_coins(coins: Seq<int>) -> int {
    if coins.len() == 5 { coins[0] + coins[1] + coins[2] + coins[3] + coins[4] } else { 0 }
}

spec fn has_valid_solution(coins: Seq<int>) -> bool {
    if valid_input(coins) {
        let total = total_coins(coins);
        total > 0 && total % 5 == 0
    } else {
        false
    }
}

spec fn compute_result(coins: Seq<int>) -> int {
    if valid_input(coins) {
        let total = total_coins(coins);
        if total > 0 && total % 5 == 0 { total / 5 } else { -1 }
    } else {
        -1
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(coins: Vec<i8>) -> (result: i8)
    requires
        valid_input(coins@.map(|i, x| x as int)),
    ensures
        result as int == compute_result(coins@.map(|i, x| x as int)),
        has_valid_solution(coins@.map(|i, x| x as int)) ==> result as int == total_coins(coins@.map(|i, x| x as int)) / 5,
        !has_valid_solution(coins@.map(|i, x| x as int)) ==> result as int == -1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}