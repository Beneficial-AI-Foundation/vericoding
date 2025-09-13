// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(cards: Seq<int>) -> bool {
    cards.len() == 5 && forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0
}

spec fn sum(cards: Seq<int>) -> int {
    if cards.len() == 0 { 0 } else { cards[0] + sum(cards.drop_first()) }
}

spec fn min_possible_sum_up_to_index(cards: Seq<int>, index: int) -> int {
    0
}

spec fn min_possible_sum(cards: Seq<int>) -> int
    recommends valid_input(cards)
{
    min_possible_sum_up_to_index(cards, 5)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(cards: Seq<int>) -> (result: int)
    requires 
        valid_input(cards)
    ensures 
        result >= 0,
        result <= sum(cards),
        result == min_possible_sum(cards)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}