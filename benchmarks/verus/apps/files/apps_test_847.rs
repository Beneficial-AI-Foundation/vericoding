// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    x > 0 && cards.len() >= 1 && forall|i: int| 0 <= i < cards.len() ==> -x <= cards[i] <= x
}
// </vc-helpers>

// <vc-spec>
fn solve(cards: Seq<int>, x: int) -> (result: int)
    requires 
        valid_input(cards, x)
    ensures 
        result >= 0,
        result == if sum(cards) == 0 { 0 } else { (abs(sum(cards)) + x - 1) / x }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}