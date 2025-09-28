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
/* helper modified by LLM (iteration 5): helper function to safely compute (k-1)*a with overflow protection and proper bounds */
fn safe_mult_k_minus_1(k: i8, a: i8) -> (result: i8)
    requires
        k >= 1,
        a >= 1,
        k == 1 || (k - 1) * (a as int) <= 127,
    ensures
        k == 1 ==> result == 0,
        k > 1 ==> result == (k - 1) * a,
        result >= 0,
{
    if k == 1 {
        0
    } else {
        (k - 1) * a
    }
}

/* helper modified by LLM (iteration 5): helper function to safely subtract with underflow protection */
fn safe_sub(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
    ensures
        result >= 0,
        result == if a >= b { a - b } else { 0 },
{
    if a >= b {
        a - b
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): helper function to safely add with overflow protection */
fn safe_add(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
        (a as int) + (b as int) <= 127,
    ensures
        result == a + b,
        result >= 0,
{
    a + b
}
// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, k1: i8, k2: i8, n: i8) -> (ret: (i8, i8))
    requires valid_input(a1 as int, a2 as int, k1 as int, k2 as int, n as int)
    ensures valid_result(a1 as int, a2 as int, k1 as int, k2 as int, n as int, ret.0 as int, ret.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use safe arithmetic operations to prevent overflow/underflow */
    let k1_minus_1_times_a1 = safe_mult_k_minus_1(k1, a1);
    let k2_minus_1_times_a2 = safe_mult_k_minus_1(k2, a2);
    let max_non_sendoff_cards = safe_add(k1_minus_1_times_a1, k2_minus_1_times_a2);
    
    let minimum = safe_sub(n, max_non_sendoff_cards);
    
    let maximum = if k1 < k2 {
        let team1_sent = if n / k1 < a1 { n / k1 } else { a1 };
        let remaining_cards = n - team1_sent * k1;
        team1_sent + remaining_cards / k2
    } else {
        let team2_sent = if n / k2 < a2 { n / k2 } else { a2 };
        let remaining_cards = n - team2_sent * k2;
        team2_sent + remaining_cards / k1
    };
    
    (minimum, maximum)
}
// </vc-code>


}

fn main() {}