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
proof fn sum_empty()
    ensures sum(Seq::<int>::empty()) == 0
{
}

proof fn sum_singleton(x: int)
    ensures sum(seq![x]) == x
{
    assert(seq![x].subrange(1, 1) =~= Seq::<int>::empty());
}

proof fn sum_append(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        sum_singleton(x);
    } else {
        assert(s.push(x).subrange(1, (s.len() + 1) as int) =~= s.subrange(1, s.len() as int).push(x));
        sum_append(s.subrange(1, s.len() as int), x);
    }
}

/* helper modified by LLM (iteration 4): Add decreases clause to while loop */
fn compute_scores(cards: &Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures scores.len() == 2,
            scores[0] as int == sereja_optimal_score(cards@.map(|i, x| x as int), 0, cards@.len() - 1, true),
            scores[1] as int == sum(cards@.map(|i, x| x as int)) - scores[0] as int
{
    let n = cards.len();
    let mut dp: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            dp.len() == i,
            forall|k: int| 0 <= k < i ==> dp[k].len() == n,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row.len() == j,
            decreases n - j
        {
            row.push(0i8);
            j = j + 1;
        }
        dp.push(row);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            dp.len() == n,
            forall|k: int| 0 <= k < n ==> dp[k].len() == n,
            forall|k: int| 0 <= k < i ==> dp[k][k] as int == cards[k] as int,
        decreases n - i
    {
        let mut row = dp[i].clone();
        row.set(i, cards[i]);
        dp.set(i, row);
        i = i + 1;
    }
    
    let mut len: usize = 2;
    while len <= n
        invariant
            2 <= len <= n + 1,
            dp.len() == n,
            forall|k: int| 0 <= k < n ==> dp[k].len() == n,
            forall|l: int, r: int| 0 <= l <= r < n && r - l + 1 < len ==>
                dp[l][r] as int == sereja_optimal_score(cards@.map(|i, x| x as int), l, r, true),
        decreases n + 1 - len
    {
        let mut left: usize = 0;
        while left + len - 1 < n
            invariant
                left <= n - len + 1,
                dp.len() == n,
                forall|k: int| 0 <= k < n ==> dp[k].len() == n,
                forall|l: int, r: int| 0 <= l <= r < n && r - l + 1 < len ==>
                    dp[l][r] as int == sereja_optimal_score(cards@.map(|i, x| x as int), l, r, true),
                forall|l: int| 0 <= l < left ==>
                    dp[l][l + len - 1] as int == sereja_optimal_score(cards@.map(|i, x| x as int), l, l + len - 1, true),
            decreases n - len + 1 - left
        {
            let right = left + len - 1;
            let take_left = if cards[left] > cards[right] {
                cards[left] + if left + 2 <= right { dp[left + 2][right] } else { 0 }
            } else {
                if left + 1 <= right - 1 { dp[left + 1][right - 1] } else { 0 }
            };
            
            let take_right = if cards[right] > cards[left] {
                cards[right] + if left <= right - 2 { dp[left][right - 2] } else { 0 }
            } else {
                if left + 1 <= right - 1 { dp[left + 1][right - 1] } else { 0 }
            };
            
            let mut row = dp[left].clone();
            row.set(right, if take_left > take_right { take_left } else { take_right });
            dp.set(left, row);
            left = left + 1;
        }
        len = len + 1;
    }
    
    let sereja_score = dp[0][n - 1];
    let mut total: i16 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            total == sum(cards@.map(|i2, x| x as int).subrange(0, i as int)),
        decreases n - i
    {
        total = total + cards[i] as i16;
        i = i + 1;
    }
    
    let dima_score = (total - sereja_score as i16) as i8;
    vec![sereja_score, dima_score]
}
// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>) -> (scores: Vec<i8>)
    requires valid_input(cards@.map(|i, x| x as int))
    ensures valid_output(scores@.map(|i, x| x as int), cards@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Call helper function to compute scores */
    let scores = compute_scores(&cards);
    scores
}
// </vc-code>


}

fn main() {}