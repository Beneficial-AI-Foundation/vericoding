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

// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures valid_output(scores@.map(|i, x| x as int), cards@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clause to loop */
{
    let n = cards.len();
    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut sereja_score: i16 = 0;
    let mut dima_score: i16 = 0;
    let mut turn = true;

    while left <= right
        invariant
            0 <= left <= right + 1,
            right < n,
            sereja_score >= 0,
            dima_score >= 0,
        decreases (right - left + 1)
    {
        let left_val = cards[left] as i16;
        let right_val = cards[right] as i16;
        if left_val > right_val {
            if turn {
                sereja_score += left_val;
            } else {
                dima_score += left_val;
            }
            left += 1;
        } else {
            if turn {
                sereja_score += right_val;
            } else {
                dima_score += right_val;
            }
            right -= 1;
        }
        turn = !turn;
    }

    let sereja_score_i8 = sereja_score as i8;
    let dima_score_i8 = dima_score as i8;
    vec![sereja_score_i8, dima_score_i8]
}
// </vc-code>


}

fn main() {}