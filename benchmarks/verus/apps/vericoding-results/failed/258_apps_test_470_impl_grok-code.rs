// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(cards: Seq<int>) -> bool {
    cards.len() == 5 && forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0
}

spec fn sum(cards: Seq<int>) -> int
    decreases cards.len()
{
    if cards.len() == 0 {
        0
    } else {
        cards[0] + sum(cards.subrange(1, cards.len() as int))
    }
}

spec fn min_possible_sum_up_to_index(cards: Seq<int>, index: int) -> int 
    decreases index when index >= 0
{
    if index <= 0 {
        sum(cards)
    } else {
        min_possible_sum_up_to_index(cards, index - 1)
    }
}

spec fn min_possible_sum(cards: Seq<int>) -> int {
    min_possible_sum_up_to_index(cards, 5)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed trailing comma from ensures clause to fix compilation error */
fn exec_sum(cards: &Vec<i8>) -> int
    requires
        cards.len() == 5,
        forall|i: int| 0 <= i < cards.len() ==> 0 < cards[i as usize] as int && cards[i as usize] as int < 128,
    ensures
        result == sum(cards@.map(|_, x: i8| x as int))
{
    let mut total: int = 0;
    let mut i: usize = 0;
    while i < 5
        invariant
            0 <= i as int <= 5,
            total == sum(cards@.take(i as int)),
    {
        total = total + cards[i] as int;
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (result: i8)
    requires 
        valid_input(cards@.map(|_index, x: i8| x as int)),
    ensures 
        result >= 0,
        result as int <= sum(cards@.map(|_index, x: i8| x as int)),
        result as int == min_possible_sum(cards@.map(|_index, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented by calling exec_sum and casting the result to i8 */
{
    let total = exec_sum(&cards);
    total as i8
}
// </vc-code>


}

fn main() {}