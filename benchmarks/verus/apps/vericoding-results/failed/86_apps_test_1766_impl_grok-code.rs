// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(cards: Seq<int>) -> bool {
    cards.len() >= 1 &&
    (forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0) &&
    (forall|i: int, j: int| 0 <= i < j < cards.len() ==> cards[i] != cards[j])
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

spec fn sereja_optimal_score(cards: Seq<int>, left: int, right: int, sereja_turn: bool) -> int
    decreases right - left + 1
    when 0 <= left <= right < cards.len()
{
    if left == right {
        if sereja_turn { cards[left] } else { 0 }
    } else if cards[left] > cards[right] {
        (if sereja_turn { cards[left] } else { 0 }) + sereja_optimal_score(cards, left+1, right, !sereja_turn)
    } else {
        (if sereja_turn { cards[right] } else { 0 }) + sereja_optimal_score(cards, left, right-1, !sereja_turn)
    }
}

spec fn valid_output(scores: Seq<int>, cards: Seq<int>) -> bool {
    valid_input(cards) ==>
    scores.len() == 2 &&
    scores[0] >= 0 && scores[1] >= 0 &&
    scores[0] + scores[1] == sum(cards) &&
    scores[0] == sereja_optimal_score(cards, 0, cards.len()-1, true) &&
    scores[1] == sum(cards) - sereja_optimal_score(cards, 0, cards.len()-1, true)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Implemented exec_sum function to compute the sum of card values and exec_sereja_score function to compute Sereja's optimal score recursively */
fn exec_sum(cards: &Vec<i8>) -> (ret: i8)
    ensures
        ret as int == sum(cards@.map(|i, x| x as int))
{
    let mut s = 0i8;
    let mut i = 0;
    while i < cards.len()
        invariant
            s as int == sum(cards@.take(i as int).map(|i, x| x as int))
    {
        s = s + cards[i];
        i = i + 1;
    }
    s
}

fn exec_sereja_score(cards: &Vec<i8>, left: usize, right: usize, sereja_turn: bool) -> (ret: i8)
    decreases right - left
    requires
        0 <= left <= right < cards.len()
    ensures
        ret as int == sereja_optimal_score(cards@.map(|i, x| x as int), left as int, right as int, sereja_turn)
{
    if left == right {
        if sereja_turn { cards[left] } else { 0 }
    } else {
        if cards[left] > cards[right] {
            let picked = if sereja_turn { cards[left] } else { 0 };
            picked + exec_sereja_score(cards, left + 1, right, !sereja_turn)
        } else {
            let picked = if sereja_turn { cards[right] } else { 0 };
            picked + exec_sereja_score(cards, left, right - 1, !sereja_turn)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures valid_output(scores@.map(|i, x| x as int), cards@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implemented the main logic to compute total sum, Sereja's optimal score, Dima's score from remaining, and return the scores */
    let total = exec_sum(&cards);
    let sereja = exec_sereja_score(&cards, 0, cards.len() - 1, true);
    let dima = total - sereja;
    let scores = vec![sereja, dima];
    scores
}
// </vc-code>


}

fn main() {}