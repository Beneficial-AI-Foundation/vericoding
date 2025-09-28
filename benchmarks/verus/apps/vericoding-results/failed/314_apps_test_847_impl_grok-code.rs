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
/* helper modified by LLM (iteration 5): increased bit width to i64 to allow larger sums and reduce overflow concerns */
exec fn compute_sum(cards: Vec<i8>, x: i8) -> (s: i64)
    requires
        valid_input(cards@.map(|i: int, v: i8| v as int), x as int),
    ensures
        s as int == sum(cards@.map(|i: int, v: i8| v as int))
{
    let mut i: usize = 0;
    let mut res: i64 = 0;
    while i < cards.len()
        invariant
            i <= cards.len(),
            res as int == sum(cards@.map(|idx: int, v: i8| v as int).subrange(0, i as int)),
        decreases (cards.len() - i)
    {
        res = res + (cards[i] as i64);
        i = i + 1;
        assert(res as int == sum(cards@.map(|idx: int, v: i8| v as int).subrange(0, i as int)));
    }
    res
}
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
/* code modified by LLM (iteration 5): adapted to use i64 for computations to handle larger values and match helper changes */
{
    let s: i64 = compute_sum(cards, x);
    let result_i64: i64 = if s == 0 {
        0
    } else {
        let abs_val: i64 = if s < 0 { -s } else { s };
        let numerator: i64 = abs_val + (x as i64) - 1;
        let denominator: i64 = x as i64;
        numerator / denominator
    };
    proof {
        assert(s as int == sum(cards@.map(|i: int, v: i8| v as int)));
        assert(result_i64 as int == if s as int == 0 { 0 } else { (abs(s as int) + (x as int) - 1) / (x as int) });
        assert((s as int == 0) == (sum(cards@.map(|i: int, v: i8| v as int)) == 0));
        assert(if s as int == 0 { 0 } else { (abs(sum(cards@.map(|i: int, v: i8| v as int))) + (x as int) - 1) / (x as int) } == solve_result(cards@.map(|i: int, v: i8| v as int), x as int));
    }
    result_i64 as i8
}
// </vc-code>


}

fn main() {}