// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a1: int, a2: int, k1: int, k2: int, n: int) -> bool {
    a1 >= 1 && a2 >= 1 && k1 >= 1 && k2 >= 1 && n >= 1
}

spec fn minimum_sent_off(a1: int, a2: int, k1: int, k2: int, n: int) -> int
    recommends valid_input(a1, a2, k1, k2, n)
{
    let max_non_sendoff_cards = (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 { n - max_non_sendoff_cards } else { 0 }
}

spec fn maximum_sent_off(a1: int, a2: int, k1: int, k2: int, n: int) -> int
    recommends valid_input(a1, a2, k1, k2, n)
{
    if k1 < k2 {
        let team1_sent = if n / k1 < a1 { n / k1 } else { a1 };
        let remaining_cards = n - team1_sent * k1;
        team1_sent + remaining_cards / k2
    } else {
        let team2_sent = if n / k2 < a2 { n / k2 } else { a2 };
        let remaining_cards = n - team2_sent * k2;
        team2_sent + remaining_cards / k1
    }
}

spec fn valid_result(a1: int, a2: int, k1: int, k2: int, n: int, minimum: int, maximum: int) -> bool
    recommends valid_input(a1, a2, k1, k2, n)
{
    minimum >= 0 && maximum >= 0 &&
    minimum <= maximum &&
    maximum <= a1 + a2 &&
    minimum <= n &&
    maximum <= n &&
    minimum == minimum_sent_off(a1, a2, k1, k2, n) &&
    maximum == maximum_sent_off(a1, a2, k1, k2, n)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, k1: i8, k2: i8, n: i8) -> (ret: (i8, i8))
    requires valid_input(a1 as int, a2 as int, k1 as int, k2 as int, n as int)
    ensures valid_result(a1 as int, a2 as int, k1 as int, k2 as int, n as int, ret.0 as int, ret.1 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added assertions in proof block to ensure positive values and prevent underflow/overflow */
{
    proof {
        assert(a1 as i32 >= 1);
        assert(a2 as i32 >= 1);
        assert(k1 as i32 >= 1);
        assert(k2 as i32 >= 1);
        assert(n as i32 >= 1);
    }
    let a1_i32 = a1 as i32;
    let a2_i32 = a2 as i32;
    let k1_i32 = k1 as i32;
    let k2_i32 = k2 as i32;
    let n_i32 = n as i32;
    
    let max_non_sendoff_i32 = (k1_i32 - 1) * a1_i32 + (k2_i32 - 1) * a2_i32;
    
    let minimum_i32: i32 = if n_i32 > max_non_sendoff_i32 { n_i32 - max_non_sendoff_i32 } else { 0 };
    
    let maximum_i32: i32;
    if k1_i32 < k2_i32 {
        let team1_sent = if n_i32 / k1_i32 < a1_i32 { n_i32 / k1_i32 } else { a1_i32 };
        let remaining = n_i32 - team1_sent * k1_i32;
        maximum_i32 = team1_sent + remaining / k2_i32;
    } else {
        let team2_sent = if n_i32 / k2_i32 < a2_i32 { n_i32 / k2_i32 } else { a2_i32 };
        let remaining = n_i32 - team2_sent * k2_i32;
        maximum_i32 = team2_sent + remaining / k1_i32;
    }
    
    proof {
        assert(minimum_i32 >= 0 && maximum_i32 >= 0);
        assert(minimum_i32 <= maximum_i32);
        assert(maximum_i32 <= a1_i32 + a2_i32);
        assert(minimum_i32 <= n_i32);
        assert(maximum_i32 <= n_i32);
        assert(minimum_i32 == minimum_sent_off(a1 as int, a2 as int, k1 as int, k2 as int, n as int));
        assert(maximum_i32 == maximum_sent_off(a1 as int, a2 as int, k1 as int, k2 as int, n as int));
    }
    
    (minimum_i32 as i8, maximum_i32 as i8)
}
// </vc-code>


}

fn main() {}