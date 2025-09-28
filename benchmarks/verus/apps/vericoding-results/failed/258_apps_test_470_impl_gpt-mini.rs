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
/* helper modified by LLM (iteration 5): prove min_possible_sum_up_to_index equals sum */
proof fn lemma_min_up_to(cards: Seq<int>, index: int)
    requires
        cards.len() == 5,
        index >= 0,
    ensures
        min_possible_sum_up_to_index(cards, index) == sum(cards),
    decreases
        index
{
    if index <= 0 {
        // By definition of min_possible_sum_up_to_index when index <= 0 it equals sum(cards)
    } else {
        lemma_min_up_to(cards, index - 1);
    }
}

/* helper modified by LLM (iteration 5): relate min_possible_sum to sum */
proof fn min_equals_sum(cards: Seq<int>)
    requires
        cards.len() == 5,
    ensures
        min_possible_sum(cards) == sum(cards),
{
    lemma_min_up_to(cards, 5);
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
    /* code modified by LLM (iteration 5): compute sum and use proofs to relate to spec */
    let mut idx: usize = 0;
    let mut acc_i32: i32 = 0;
    while idx < cards.len()
        invariant
            0 <= idx as int,
            idx as int <= cards@.len(),
            acc_i32 as int == sum(cards@.map(|_i, x: i8| x as int).subrange(0, idx as int)),
        decreases
            cards.len() - idx
    {
        acc_i32 = acc_i32 + cards[idx] as i32;
        idx = idx + 1;
    }
    let result = acc_i32 as i8;
    proof {
        let s = cards@.map(|_i, x: i8| x as int);
        assert(acc_i32 as int == sum(s));
        min_equals_sum(s);
        assert(result as int == min_possible_sum(s));
        assert(result as int <= sum(s));
        assert(result >= 0);
    }
    result
}

// </vc-code>


}

fn main() {}