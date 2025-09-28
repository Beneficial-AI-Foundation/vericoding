// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(scores: Seq<int>) -> bool {
    scores.len() > 0 && scores.len() <= 100 &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 1 && #[trigger] scores[i] <= 100
}

spec fn sum_seq(scores: Seq<int>) -> int
    decreases scores.len()
{
    if scores.len() == 0 {
        0
    } else {
        scores[0] + sum_seq(scores.subrange(1, scores.len() as int))
    }
}

spec fn all_multiples_of_10(scores: Seq<int>) -> bool {
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] % 10 == 0
}

spec fn is_smallest_non_multiple(scores: Seq<int>, value: int) -> bool {
    scores.contains(value) && 
    value % 10 != 0 &&
    forall|x: int| #[trigger] scores.contains(x) && x % 10 != 0 ==> value <= x
}

spec fn correct_result(scores: Seq<int>, result: int) -> bool {
    let total_sum = sum_seq(scores);
    if total_sum % 10 != 0 {
        result == total_sum
    } else if all_multiples_of_10(scores) {
        result == 0
    } else {
        exists|smallest_non_multiple: int| 
            is_smallest_non_multiple(scores, smallest_non_multiple) &&
            result == total_sum - smallest_non_multiple
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_seq_append(s1: Seq<int>, s2: Seq<int>)
    requires s1.len() > 0
    ensures sum_seq(s1 + s2) == s1[0] + sum_seq(s1.subrange(1, s1.len() as int) + s2)
    decreases s1.len()
{
    /* helper modified by LLM (iteration 5): added proof by revealing definition */
    reveal(sum_seq);
}

proof fn lemma_sum_seq_single(x: int)
    ensures sum_seq(seq![x]) == x
{
    /* helper modified by LLM (iteration 5): added proof by revealing definition */
    reveal(sum_seq);
}

proof fn lemma_sum_seq_empty()
    ensures sum_seq(seq![]) == 0
{
    /* helper modified by LLM (iteration 5): added proof by revealing definition */
    reveal(sum_seq);
}

fn find_smallest_non_multiple(scores: &Vec<i8>) -> (result: Option<i8>)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures match result {
        Some(val) => {
            let scores_int = scores@.map(|i, x| x as int);
            scores_int.contains(val as int) && val % 10 != 0 &&
            forall|x: int| #[trigger] scores_int.contains(x) && x % 10 != 0 ==> (val as int) <= x
        },
        None => all_multiples_of_10(scores@.map(|i, x| x as int))
    }
{
    let mut smallest: Option<i8> = None;
    let mut i = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            match smallest {
                Some(val) => val % 10 != 0 && val >= 1 && val <= 100 &&
                           exists|j: int| 0 <= j < i && scores@[j] == val &&
                           forall|k: int| 0 <= k < i && (scores@[k] as int) % 10 != 0 ==> (val as int) <= (scores@[k] as int),
                None => forall|k: int| 0 <= k < i ==> (scores@[k] as int) % 10 == 0
            }
        decreases scores.len() - i
    {
        let score = scores[i];
        if score % 10 != 0 {
            match smallest {
                Some(current_smallest) => {
                    if score < current_smallest {
                        smallest = Some(score);
                    }
                },
                None => {
                    smallest = Some(score);
                }
            }
        }
        i += 1;
    }
    
    smallest
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax */
    let mut total_sum: i32 = 0;
    let mut i = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            total_sum == sum_seq(scores@.subrange(0, i as int).map(|j, x| x as int)),
            total_sum >= 0,
            total_sum <= 10000
        decreases scores.len() - i
    {
        total_sum = total_sum + (scores[i] as i32);
        
        // Prove the invariant holds
        proof {
            lemma_sum_seq_append(
                scores@.subrange(0, i as int).map(|j, x| x as int),
                seq![scores@[i as int] as int]
            );
        }
        
        i += 1;
    }
    
    if total_sum % 10 != 0 {
        return total_sum as i8;
    }
    
    let smallest_non_multiple = find_smallest_non_multiple(&scores);
    
    match smallest_non_multiple {
        Some(val) => {
            (total_sum - val as i32) as i8
        },
        None => {
            0
        }
    }
}
// </vc-code>


}

fn main() {}