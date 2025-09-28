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
spec fn number_unique(scores: Seq<i8>) -> nat {
    let set = Set::new(|x: int| exists|i: int| 0 <= i < scores.len() && scores[i] as int != 0 && scores[i] as int == x);
    set.len()
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented loop to count unique non-zero scores with proper invariants */
    let mut unique_scores: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < scores.len()
        invariant
            forall|k: int| 0 <= k < i as int ==> scores@[k] != 0 ==> exists|j: int| 0 <= j < unique_scores@.len() && unique_scores@[j] as int == scores@[k] as int,
            unique_scores@.len() == number_unique(scores@.subrange(0, i as int)),
            forall|k: int| 0 <= k < i as int ==> unique_scores@[k] != 0,
            forall|k: int| 0 <= k < unique_scores@.len() ==> exists|l: int| 0 <= l < i as int && scores@[l] as int == unique_scores@[k] as int,
            forall|j: int, m: int| 0 <= j < m < unique_scores@.len() ==> unique_scores@[j] != unique_scores@[m],
        decreases ((scores@.len() as int) - (i as int))
    {
        if scores[i] != 0 {
            let mut found = false;
            let mut j: usize = 0;
            while j < unique_scores.len()
                invariant
                    0 <= j <= unique_scores.len(),
                    found == exists|k: int| 0 <= k < j as int && unique_scores@[k] as int == scores[i] as int,
                decreases ((unique_scores@.len() as int) - (j as int))
            {
                if unique_scores[j] == scores[i] {
                    found = true;
                    break;
                }
                j += 1;
            }
            if !found {
                unique_scores.push(scores[i]);
            }
        }
        i += 1;
    }
    let result = unique_scores.len() as i8;
    result
}
// </vc-code>


}

fn main() {}