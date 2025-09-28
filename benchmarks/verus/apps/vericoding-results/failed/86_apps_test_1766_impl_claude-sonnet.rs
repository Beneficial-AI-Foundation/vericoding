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
/* helper modified by LLM (iteration 5): fixed type mismatches in array indexing */
fn sereja_game_recursive(cards: &Vec<i8>, left: usize, right: usize, sereja_turn: bool) -> (score: i8)
    requires
        cards.len() >= 1,
        left <= right,
        right < cards.len(),
        forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0,
        forall|i: int, j: int| 0 <= i < j < cards.len() ==> cards[i] != cards[j],
        forall|i: int| 0 <= i < cards.len() ==> cards[i] <= 100
    ensures
        score == sereja_optimal_score(cards@.map(|i, x| x as int), left as int, right as int, sereja_turn),
        score >= 0
    decreases right - left + 1
{
    if left == right {
        if sereja_turn { cards[left] } else { 0 }
    } else {
        if sereja_turn {
            if cards[left] > cards[right] {
                let sub_score = sereja_game_recursive(cards, left + 1, right, false);
                proof {
                    assert(sub_score <= 100 * (cards.len() as i8));
                    assert(cards@[left as int] as i32 + sub_score as i32 <= 127);
                }
                cards[left] + sub_score
            } else {
                let sub_score = sereja_game_recursive(cards, left, right - 1, false);
                proof {
                    assert(sub_score <= 100 * (cards.len() as i8));
                    assert(cards@[right as int] as i32 + sub_score as i32 <= 127);
                }
                cards[right] + sub_score
            }
        } else {
            if cards[left] > cards[right] {
                sereja_game_recursive(cards, left + 1, right, true)
            } else {
                sereja_game_recursive(cards, left, right - 1, true)
            }
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
    /* code modified by LLM (iteration 5): fixed type mismatches in array indexing */
    // Establish bounds
    proof {
        assert(cards.len() >= 1);
        let cards_spec = cards@.map(|i, x| x as int);
        assert(forall|i: int| 0 <= i < cards.len() ==> cards[i] > 0);
        assert(forall|i: int| 0 <= i < cards.len() ==> cards[i] <= 127);
        assert(forall|i: int| 0 <= i < cards.len() ==> cards[i] <= 100); // strengthen bound
    }
    
    let sereja_score = sereja_game_recursive(&cards, 0, cards.len() - 1, true);
    
    let mut total_sum: i32 = 0;
    let mut i = 0;
    while i < cards.len()
        invariant
            i <= cards.len(),
            total_sum == sum(cards@.subrange(0, i as int).map(|j, x| x as int)),
            total_sum >= 0,
            total_sum <= i as i32 * 127
        decreases cards.len() - i
    {
        proof {
            assert(cards@[i as int] as i32 >= 1);
            assert(cards@[i as int] as i32 <= 127);
            assert(total_sum + cards@[i as int] as i32 <= (i + 1) as i32 * 127);
        }
        total_sum = total_sum + cards[i] as i32;
        i = i + 1;
    }
    
    proof {
        assert(total_sum <= cards.len() as i32 * 127);
        assert(sereja_score as i32 <= total_sum);
        assert(total_sum - sereja_score as i32 >= 0);
        assert(total_sum - sereja_score as i32 <= 127);
    }
    
    #[verifier::truncate]
    let dima_score = (total_sum - sereja_score as i32) as i8;
    
    let mut result = Vec::new();
    result.push(sereja_score);
    result.push(dima_score);
    
    proof {
        let cards_spec = cards@.map(|i, x| x as int);
        let result_spec = result@.map(|i, x| x as int);
        assert(result@.len() == 2);
        assert(result_spec[0] == sereja_score as int);
        assert(result_spec[1] == dima_score as int);
        assert(sereja_score as int == sereja_optimal_score(cards_spec, 0, cards.len()-1, true));
        assert(total_sum == sum(cards_spec));
        assert(sereja_score as int + dima_score as int == total_sum as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}