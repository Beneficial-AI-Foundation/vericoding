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
/* helper modified by LLM (iteration 5): [No changes needed in helpers] */
pub open spec fn get_sereja_score_dp(cards: Seq<int>, i: int, j: int) -> int {
    if i == j {
        cards[i]
    } else if cards[i] > cards[j] {
        cards[i] + get_dima_score_dp(cards, i + 1, j)
    } else {
        cards[j] + get_dima_score_dp(cards, i, j - 1)
    }
}

pub open spec fn get_dima_score_dp(cards: Seq<int>, i: int, j: int) -> int {
    if i == j {
        0
    } else if cards[i] > cards[j] {
        get_sereja_score_dp(cards, i + 1, j)
    } else {
        get_sereja_score_dp(cards, i, j - 1)
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures valid_output(scores@.map(|i, x| x as int), cards@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed compilation error by replacing `ghost Map` with `Map` for proper Verus `Map` usage. Ensured correct types for map operations.] */
{
    let n = cards.len() as int;
    let cards_seq = cards@.map(|i, x| x as int);

    let mut dp_sereja: Map<int, Map<int, int>> = Map::empty();
    let mut dp_dima: Map<int, Map<int, int>> = Map::empty();

    if n == 0 {
        return Vec::new();
    }

    for i in 0..n
        invariant
            0 <= i <= n,
            forall|k: int|
                0 <= k < i ==> dp_sereja.dom().contains(k) && dp_dima.dom().contains(k)
                && dp_sereja[k].dom().contains(k)
                && dp_dima[k].dom().contains(k)
                && dp_sereja[k][k] == cards_seq[k]
                && dp_dima[k][k] == 0,
            dp_sereja.dom().subset_of((0..n).to_set()),
            dp_dima.dom().subset_of((0..n).to_set()),
    {
        dp_sereja = dp_sereja.insert(i, Map::empty().insert(i, cards_seq[i]));
        dp_dima = dp_dima.insert(i, Map::empty().insert(i, 0));
    }

    for len in 2..=(n as int)
        invariant
            2 <= len <= n + 1,
            dp_sereja.dom().subset_of((0..n).to_set()),
            dp_dima.dom().subset_of((0..n).to_set()),
            forall|idx: int|
                0 <= idx < n ==> dp_sereja.dom().contains(idx) && dp_dima.dom().contains(idx),
            forall|i_idx: int, j_idx: int|
                0 <= i_idx <= j_idx < n
                && j_idx - i_idx + 1 < len
                ==>
                    dp_sereja[i_idx].dom().contains(j_idx)
                    && dp_dima[i_idx].dom().contains(j_idx)
                    && dp_sereja[i_idx][j_idx] == get_sereja_score_dp(cards_seq, i_idx, j_idx)
                    && dp_dima[i_idx][j_idx] == get_dima_score_dp(cards_seq, i_idx, j_idx),

    {
        for i in 0..=(n - len as int)
            invariant
                0 <= i <= n - len as int + 1,
                dp_sereja.dom().subset_of((0..n).to_set()),
                dp_dima.dom().subset_of((0..n).to_set()),
                forall|idx: int|
                    0 <= idx < n ==> dp_sereja.dom().contains(idx) && dp_dima.dom().contains(idx),
                forall|i_idx: int, j_idx: int|
                    0 <= i_idx <= j_idx < n
                    && j_idx - i_idx + 1 < len
                    ==>
                        dp_sereja[i_idx].dom().contains(j_idx)
                        && dp_dima[i_idx].dom().contains(j_idx)
                        && dp_sereja[i_idx][j_idx] == get_sereja_score_dp(cards_seq, i_idx, j_idx)
                        && dp_dima[i_idx][j_idx] == get_dima_score_dp(cards_seq, i_idx, j_idx),
                forall|i_idx: int|
                    0 <= i_idx < i
                    ==>
                        ({let current_j = i_idx + len - 1;
                        current_j < n
                        ==> dp_sereja[i_idx].dom().contains(current_j)
                        && dp_dima[i_idx].dom().contains(current_j)
                        && dp_sereja[i_idx][current_j] == get_sereja_score_dp(cards_seq, i_idx, current_j)
                        && dp_dima[i_idx][current_j] == get_dima_score_dp(cards_seq, i_idx, current_j)}) ,
        {
            let j = i + len - 1;

            let score_sereja_take_left = cards_seq[i] + dp_dima[i + 1][j];
            let score_dima_take_left = dp_sereja[i + 1][j];

            let score_sereja_take_right = cards_seq[j] + dp_dima[i][j - 1];
            let score_dima_take_right = dp_sereja[i][j - 1];

            let sereja_val;
            let dima_val;

            if score_sereja_take_left >= score_sereja_take_right {
                sereja_val = score_sereja_take_left;
                dima_val = score_dima_take_left;
            } else {
                sereja_val = score_sereja_take_right;
                dima_val = score_dima_take_right;
            }
            dp_sereja = dp_sereja.insert(i as int, dp_sereja[i as int].insert(j as int, sereja_val));
            dp_dima = dp_dima.insert(i as int, dp_dima[i as int].insert(j as int, dima_val));
        }
    }

    let mut scores = Vec::new();
    scores.push(dp_sereja[0][(n - 1) as int] as i8);
    scores.push(dp_dima[0][(n - 1) as int] as i8);

    proof {
        if n > 0 {
            let sereja_final_score = dp_sereja[0][(n - 1) as int];
            let dima_final_score = dp_dima[0][(n - 1) as int];
            assert(sereja_final_score == sereja_optimal_score(cards_seq, 0, (n - 1) as int, true));
            assert(dima_final_score == sum(cards_seq) - sereja_optimal_score(cards_seq, 0, (n - 1) as int, true));
        }
    }

    scores
}

// </vc-code>


}

fn main() {}