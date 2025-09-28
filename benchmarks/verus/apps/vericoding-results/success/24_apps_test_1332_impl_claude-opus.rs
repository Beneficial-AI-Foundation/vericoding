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
    /* code modified by LLM (iteration 2): Fixed ghost type usage - work with i8 values directly */
    assert(coins.len() == 5);
    
    let total: i16 = coins[0] as i16 + coins[1] as i16 + coins[2] as i16 + coins[3] as i16 + coins[4] as i16;
    
    proof {
        let coin_seq = coins@.map(|i, x| x as int);
        assert(coin_seq.len() == 5);
        assert(total as int == coin_seq[0] + coin_seq[1] + coin_seq[2] + coin_seq[3] + coin_seq[4]);
        assert(total as int == total_coins(coin_seq));
    }
    
    if total > 0 && total % 5 == 0 {
        let result = (total / 5) as i8;
        proof {
            let coin_seq = coins@.map(|i, x| x as int);
            assert(total as int > 0 && total as int % 5 == 0);
            assert(has_valid_solution(coin_seq));
            assert(result as int == total as int / 5);
            assert(result as int == compute_result(coin_seq));
        }
        result
    } else {
        proof {
            let coin_seq = coins@.map(|i, x| x as int);
            assert(!has_valid_solution(coin_seq));
            assert(compute_result(coin_seq) == -1);
        }
        -1i8
    }
}
// </vc-code>


}

fn main() {}