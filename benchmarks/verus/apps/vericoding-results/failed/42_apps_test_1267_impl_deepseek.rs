// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, scores: Seq<int>) -> bool {
    n == scores.len() && n >= 1 && exists|i: int| 0 <= i < scores.len() && scores[i] != 0
}

spec fn unique_non_zero_scores(scores: Seq<int>) -> Set<int> {
    Set::new(|x: int| exists|i: int| 0 <= i < scores.len() && scores[i] != 0 && scores[i] == x)
}

spec fn valid_result(scores: Seq<int>, result: int) -> bool {
    result >= 1 && 
    result == unique_non_zero_scores(scores).len() && 
    result <= scores.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add decreases clauses for sorting loops */
spec fn count_non_zero_unique(scores: Seq<int>) -> int {
    unique_non_zero_scores(scores).len() as int
}

spec fn seq_sorted(scores: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < scores.len() ==> scores[i] <= scores[j]
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add decreases clause to outer sorting loop */
{
    let mut sorted_scores = scores.clone();
    let mut i: usize = 0;
    
    while i < sorted_scores.len()
        decreases sorted_scores.len() - i
    {
        let mut j: usize = i + 1;
        while j < sorted_scores.len()
            decreases sorted_scores.len() - j
        {
            if sorted_scores[j] < sorted_scores[i] {
                let temp = sorted_scores[i];
                sorted_scores[i] = sorted_scores[j];
                sorted_scores[j] = temp;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    let mut prev: i8 = 0;
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < sorted_scores.len()
        invariant
            0 <= i <= sorted_scores.len(),
            count >= 0,
            count as int == count_non_zero_unique(sorted_scores@.map(|idx, x| x as int).subrange(0, i as int)),
            seq_sorted(sorted_scores@.map(|idx, x| x as int))
        decreases sorted_scores.len() - i
    {
        if sorted_scores[i] != 0 {
            if i == 0 || sorted_scores[i] != prev {
                count = count + 1;
            }
            prev = sorted_scores[i];
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}