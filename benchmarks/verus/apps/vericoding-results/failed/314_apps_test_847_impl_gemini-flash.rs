// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(cards: Seq<int>) -> int
    decreases cards.len()
{
    if cards.len() == 0 {
        0
    } else {
        cards[0] + sum(cards.subrange(1, cards.len() as int))
    }
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn valid_input(cards: Seq<int>, x: int) -> bool {
    x > 0 && cards.len() >= 1 && forall|i: int| 0 <= i < cards.len() ==> #[trigger] cards[i] >= -x && #[trigger] cards[i] <= x
}

spec fn solve_result(cards: Seq<int>, x: int) -> int {
    if sum(cards) == 0 { 0 } else { (abs(sum(cards)) + x - 1) / x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in helpers. */

// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>, x: i8) -> (result: i8)
    requires 
        valid_input(cards@.map(|i: int, v: i8| v as int), x as int),
    ensures 
        result as int >= 0,
        result as int == solve_result(cards@.map(|i: int, v: i8| v as int), x as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type issues by ensuring that `current_sum` is cast to `int` only for ghost `invariant` conditions and `abs` calculations, while runtime operations remain `i8`. Simplified while loop invariants to prevent overflow and underflow errors in the loop body. The core logic for adjusting `current_sum` by `x` should maintain `current_sum` within the `[-x, x]` range for `i8` types by ensuring that its value never strays too far from `0`. The `abs` function now is called with a ghost integer, then converted back to `i8`. */
{
    let mut current_sum: i8 = 0;
    let mut i: usize = 0;
    let x_int: int = x as int;

    while i < cards.len()
        invariant
            0 <= i,
            i <= cards.len(),
            current_sum as int == sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) % x_int + if sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) % x_int == 0 && sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) != 0 && sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) > 0 { x_int } else if sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) % x_int == 0 && sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) != 0 && sum(cards@.map(|idx, v: i8| v as int).subrange(0, i as int)) < 0 { -x_int } else { 0 },
            current_sum as int >= -x_int,
            current_sum as int <= x_int,
        decreases cards.len() - i
    {
        current_sum = current_sum + cards[i];

        while current_sum as int > x_int
            invariant
                current_sum as int > x_int - (x as int),
                current_sum as int >= -(x as int),
                current_sum as int <= (x as int) + (x as int),
                i <= cards.len(),
            decreases current_sum as int
        {
            current_sum = current_sum - x;
        }
        while current_sum as int < -x_int
            invariant
                current_sum as int < -x_int + (x as int),
                current_sum as int >= -(x as int) - (x as int),
                current_sum as int <= (x as int),
                i <= cards.len(),
            decreases -(current_sum as int)
        {
            current_sum = current_sum + x;
        }
        i = i + 1;
    }
    
    let current_sum_ghost = current_sum as int;
    if current_sum_ghost == 0 { 0i8 } else { ((abs(current_sum_ghost) + x_int - 1) / x_int) as i8 }
}
// </vc-code>


}

fn main() {}