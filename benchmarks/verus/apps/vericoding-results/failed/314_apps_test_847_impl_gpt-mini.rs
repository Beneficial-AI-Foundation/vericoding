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
/* helper modified by LLM (iteration 5): provide spec mapping from Vec<i8> to Seq<int> */
spec fn vec_map(cards: Vec<i8>) -> Seq<int>
    decreases cards.len()
{
    cards@.map(|i: int, v: i8| v as int)
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
{
    /* code modified by LLM (iteration 5): compute sum with tracked int and return ceil-div result */
    let n: usize = cards.len();
    let mut i: usize = 0;
    let mut s: int = tracked 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            s == sum(vec_map(cards).subrange(0, i as int)),
        decreases n - i
    {
        let v: i8 = cards[i];
        s = s + (v as int);
        i = i + 1;
    }
    if s == 0 {
        0 as i8
    } else {
        let x_int: int = tracked (x as int);
        let r: int = (abs(s) + x_int - 1) / x_int;
        r as i8
    }
}
// </vc-code>


}

fn main() {}