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

proof fn min_possible_sum_decreases(cards: Seq<int>, index: int) 
    requires 
        cards.len() == 5,
        forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0,
        0 <= index <= 5
    ensures 
        min_possible_sum_up_to_index(cards, index) == sum(cards)
{
    if index > 0 {
        min_possible_sum_decreases(cards, index - 1);
    }
}

proof fn sum_non_negative(cards: Seq<int>) 
    requires 
        cards.len() == 5,
        forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0
    ensures 
        sum(cards) > 0
{
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
{
    /* code modified by LLM (iteration 5): Simplified implementation and fixed loop invariant */
    let mut total: i32 = 0;
    let mut i = 0;
    while i < cards.len()
        invariant
            0 <= i <= cards.len(),
            total == sum(cards@.map(|j, x| x as int).subrange(0, i as int))
    {
        total = total + cards[i] as i32;
        i = i + 1;
    }
    total as i8
}
// </vc-code>


}

fn main() {}