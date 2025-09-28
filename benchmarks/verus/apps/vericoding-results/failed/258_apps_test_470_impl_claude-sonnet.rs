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
/* helper modified by LLM (iteration 4): Removed decreases_when from proof function */
// Helper lemma to prove properties about sum
proof fn sum_lemma(cards: Seq<int>)
    requires
        cards.len() >= 0,
    ensures
        sum(cards) >= 0,
{
    if cards.len() == 0 {
        // Base case: empty sequence has sum 0
    } else {
        // Recursive case
        sum_lemma(cards.subrange(1, cards.len() as int));
    }
}

// Helper lemma about min_possible_sum_up_to_index
proof fn min_possible_sum_lemma(cards: Seq<int>, index: int)
    requires
        index >= 0,
        cards.len() >= 0,
    ensures
        min_possible_sum_up_to_index(cards, index) == sum(cards),
    decreases index
{
    if index <= 0 {
        // Base case
    } else {
        // Recursive case
        min_possible_sum_lemma(cards, index - 1);
    }
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
    /* code modified by LLM (iteration 4): Fixed ghost variable declaration syntax */
    let ghost int_cards = cards@.map(|_index, x: i8| x as int);
    
    // Calculate the sum by iterating through the vector
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < cards.len()
        invariant
            i <= cards.len(),
            total >= 0,
            total == sum(int_cards.subrange(0, i as int)),
        decreases cards.len() - i
    {
        total = total + (cards[i] as i32);
        i = i + 1;
    }
    
    proof {
        // Prove that total equals the sum of all cards
        assert(int_cards.subrange(0, cards.len() as int) == int_cards);
        
        // Prove min_possible_sum equals sum
        min_possible_sum_lemma(int_cards, 5);
        assert(min_possible_sum(int_cards) == sum(int_cards));
    }
    
    total as i8
}
// </vc-code>


}

fn main() {}