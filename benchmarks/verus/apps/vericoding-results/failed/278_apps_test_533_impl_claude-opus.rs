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
{
    /* code modified by LLM (iteration 5): Added overflow prevention assertions for i8 arithmetic */
    // Calculate minimum sent off
    let k1_minus_1 = k1 - 1;
    let k2_minus_1 = k2 - 1;
    
    // Assert bounds to prevent overflow
    assert(k1_minus_1 >= 0);
    assert(k2_minus_1 >= 0);
    assert(a1 >= 1 && a1 <= 127);
    assert(a2 >= 1 && a2 <= 127);
    assert(k1_minus_1 <= 126);
    assert(k2_minus_1 <= 126);
    
    // These assertions help Verus verify no overflow
    assert(k1_minus_1 * a1 >= 0);
    assert(k2_minus_1 * a2 >= 0);
    assert(k1_minus_1 * a1 <= 127 * 127);
    assert(k2_minus_1 * a2 <= 127 * 127);
    
    let prod1 = k1_minus_1 * a1;
    let prod2 = k2_minus_1 * a2;
    
    // Since i8 max is 127, we need to be careful with the sum
    let max_non_sendoff_cards = if prod1 <= 127 - prod2 {
        prod1 + prod2
    } else {
        127  // Cap at i8 max if overflow would occur
    };
    
    let minimum = if n > max_non_sendoff_cards { 
        n - max_non_sendoff_cards
    } else { 
        0 
    };
    
    // Calculate maximum sent off
    let maximum = if k1 < k2 {
        let team1_sent = if n / k1 < a1 { 
            n / k1
        } else { 
            a1 
        };
        let remaining_cards = n - team1_sent * k1;
        let team2_sent = if remaining_cards / k2 < a2 { 
            remaining_cards / k2
        } else { 
            a2 
        };
        team1_sent + team2_sent
    } else {
        let team2_sent = if n / k2 < a2 { 
            n / k2
        } else { 
            a2 
        };
        let remaining_cards = n - team2_sent * k2;
        let team1_sent = if remaining_cards / k1 < a1 { 
            remaining_cards / k1
        } else { 
            a1 
        };
        team2_sent + team1_sent
    };
    
    (minimum, maximum)
}
// </vc-code>


}

fn main() {}