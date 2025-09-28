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
/* helper modified by LLM (iteration 4): Removed the incorrect `sort_seq` implementation as it's not needed. The `solve` function should correctly use the sorted array properties without complex custom sorting logic. The original thought process was to use `vstd::slice::sort`, which means I should not provide a custom sort_seq. */

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
/* code modified by LLM (iteration 4): Refined the while loop conditions and invariants. Changed the logic to calculate the minimum sum directly as per the problem description (summing the 'cards' in sorted order to obtain the minimum possible sum). The `max_possible_sum` and its related logic were removed as it's not relevant to computing `min_possible_sum`. The key invariant was to ensure that the `current_sum` correctly reflected the sum of the smallest elements as we iterate, and that the cards were properly sorted. */
{
    let ghost cards_seq = cards@.map(|_index, x: i8| x as int);
    let mut cards_vec = cards; 
    cards_vec.sort(); 

    let mut current_sum: i8 = 0;

    let mut i: int = 0;
    while i < cards_vec.len()
        invariant 
            0 <= i && i <= cards_vec.len(),
            cards_vec.len() == 5,
            forall|j: int| 0 <= j && j < cards_vec.len() ==> cards_vec[j] > 0,
            // sorted property
            forall|j: int, k: int| 0 <= j && j < k && k < cards_vec.len() ==> cards_vec[j] <= cards_vec[k],
            // The sum of the first `i` elements of the sorted vector
            current_sum as int == sum(cards_vec@.subrange(0, i as int).map(|_k, x: i8| x as int)),
            cards_vec@.map(|_idx, x: i8| x as int) == vstd::seq::sort(cards_seq),
        decreases cards_vec.len() as int - i
    {
        current_sum = current_sum + cards_vec[i as usize];
        i = i + 1;
    }

    let result: i8 = current_sum;
    result
}
// </vc-code>


}

fn main() {}