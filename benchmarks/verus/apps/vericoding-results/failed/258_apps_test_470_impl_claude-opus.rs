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
/* helper modified by LLM (iteration 5): Added lemmas for sum properties and bounds */
proof fn lemma_sum_up_to_equals_sum(cards: Seq<int>, n: int)
    requires
        n == cards.len(),
    ensures
        sum_up_to(cards, n) == sum(cards),
    decreases n
{
    if n <= 0 {
        assert(cards.len() == 0);
        assert(sum_up_to(cards, n) == 0);
        assert(sum(cards) == 0);
    } else {
        assert(sum_up_to(cards, n) == cards[n - 1] + sum_up_to(cards, n - 1));
        lemma_sum_up_to_equals_sum(cards.subrange(0, n - 1 as int), n - 1);
        assert(sum(cards) == cards[0] + sum(cards.subrange(1, cards.len() as int)));
    }
}

spec fn sum_up_to(cards: Seq<int>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        cards[n - 1] + sum_up_to(cards, n - 1)
    }
}

proof fn lemma_min_possible_sum_is_sum(cards: Seq<int>)
    ensures
        min_possible_sum(cards) == sum(cards),
{
    assert(min_possible_sum(cards) == min_possible_sum_up_to_index(cards, 5));
    lemma_min_possible_sum_up_to_index_is_sum(cards, 5);
}

proof fn lemma_min_possible_sum_up_to_index_is_sum(cards: Seq<int>, index: int)
    ensures
        min_possible_sum_up_to_index(cards, index) == sum(cards),
    decreases index when index >= 0
{
    if index <= 0 {
        assert(min_possible_sum_up_to_index(cards, index) == sum(cards));
    } else {
        lemma_min_possible_sum_up_to_index_is_sum(cards, index - 1);
        assert(min_possible_sum_up_to_index(cards, index) == min_possible_sum_up_to_index(cards, index - 1));
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
    /* code modified by LLM (iteration 5): Use i32 for sum to avoid overflow, prove postconditions */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    let cards_int = cards@.map(|_index, x: i8| x as int);
    
    while i < 5
        invariant
            i <= 5,
            cards.len() == 5,
            valid_input(cards_int),
            sum as int == sum_up_to(cards_int, i as int),
            sum >= 0,
            sum <= 127 * i as i32,
        decreases 5 - i
    {
        sum = sum + cards[i] as i32;
        i = i + 1;
    }
    
    proof {
        assert(i == 5);
        assert(sum as int == sum_up_to(cards_int, 5));
        lemma_sum_up_to_equals_sum(cards_int, 5);
        assert(sum as int == sum(cards_int));
        lemma_min_possible_sum_is_sum(cards_int);
        assert(min_possible_sum(cards_int) == sum(cards_int));
        assert(sum as int == min_possible_sum(cards_int));
        assert(sum >= 0);
        assert(sum <= 127 * 5);
        assert(sum <= 127);
    }
    
    sum as i8
}
// </vc-code>


}

fn main() {}