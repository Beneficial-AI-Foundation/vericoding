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

/* helper modified by LLM (iteration 5): Added missing result variable declaration */
proof fn sereja_optimal_score_correct(cards: Seq<int>, left: int, right: int, sereja_turn: bool) -> (int, int)
    requires
        0 <= left <= right < cards.len(),
    ensures
        result.0 == sum(cards.subrange(left, right + 1)),
        result.1 == sereja_optimal_score(cards, left, right, sereja_turn),
        result.1 <= result.0,
    decreases right - left + 1
{
    let result: (int, int);
    if left == right {
        let score = if sereja_turn { cards[left] } else { 0 };
        result = (cards[left], score);
    } else {
        if cards[left] > cards[right] {
            let (sub_total, sub_score) = sereja_optimal_score_correct(cards, left + 1, right, !sereja_turn);
            let total_here = cards[left] + sub_total;
            let score_here = (if sereja_turn { cards[left] } else { 0 }) + sub_score;
            result = (total_here, score_here);
        } else {
            let (sub_total, sub_score) = sereja_optimal_score_correct(cards, left, right - 1, !sereja_turn);
            let total_here = cards[right] + sub_total;
            let score_here = (if sereja_turn { cards[right] } else { 0 }) + sub_score;
            result = (total_here, score_here);
        }
    }
    result
}

proof fn total_score_matches_sereja_optimal(cards: Seq<int>) 
    requires
        cards.len() >= 1,
        forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0,
        forall|i: int, j: int| 0 <= i < j < cards.len() ==> cards[i] != cards[j]
    ensures
        sereja_optimal_score(cards, 0, cards.len() - 1, true) + sereja_optimal_score(cards, 0, cards.len() - 1, false) == sum(cards)
{
    let (total, sereja_score) = sereja_optimal_score_correct(cards, 0, cards.len() - 1, true);
    let (_, dima_score) = sereja_optimal_score_correct(cards, 0, cards.len() - 1, false);
    assert(sum(cards) == total);
    assert(sereja_score + dima_score == total);
}

// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures valid_output(scores@.map(|i, x| x as int), cards@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added result variable to satisfy verification */
    let mut left = 0;
    let mut right = cards.len() - 1;
    let mut sereja_turn = true;
    let mut sereja_total: i8 = 0;
    let mut dima_total: i8 = 0;
    
    while left <= right {
        if sereja_turn {
            if cards[left] > cards[right] {
                sereja_total = sereja_total + cards[left];
                left = left + 1;
            } else {
                sereja_total = sereja_total + cards[right];
                right = right - 1;
            }
        } else {
            if cards[left] > cards[right] {
                dima_total = dima_total + cards[left];
                left = left + 1;
            } else {
                dima_total = dima_total + cards[right];
                right = right - 1;
            }
        }
        sereja_turn = !sereja_turn;
    }
    
    let result = vec![sereja_total, dima_total];
    result
}
// </vc-code>


}

fn main() {}