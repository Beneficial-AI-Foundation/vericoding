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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotations for quantifier inference */
    let mut unique_scores: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            n as usize == scores.len(),
            n >= 1,
            exists|j: int| 0 <= j < scores.len() && scores@[j] != 0,
            forall|k: int, l: int| 0 <= k < unique_scores.len() && 0 <= l < unique_scores.len() && k != l ==> unique_scores@[k] != unique_scores@[l],
            forall|k: int| 0 <= k < unique_scores.len() ==> unique_scores@[k] != 0,
            forall|k: int| 0 <= k < unique_scores.len() ==> exists|j: int| 0 <= j < i && scores@[j] == unique_scores@[k],
            forall|j: int| 0 <= j < i && scores@[j] != 0 ==> exists|k: int| 0 <= k < unique_scores.len() && unique_scores@[k] == scores@[j],
            unique_scores.len() <= i,
        decreases scores.len() - i
    {
        if scores[i] != 0 {
            let mut already_exists = false;
            let mut j: usize = 0;
            
            while j < unique_scores.len()
                invariant
                    0 <= j <= unique_scores.len(),
                    !already_exists ==> forall|k: int| 0 <= k < j ==> unique_scores@[k] != scores@[i as int],
                    already_exists ==> exists|k: int| 0 <= k < unique_scores.len() && unique_scores@[k] == scores@[i as int],
                decreases unique_scores.len() - j
            {
                if unique_scores[j] == scores[i] {
                    already_exists = true;
                }
                j = j + 1;
            }
            
            if !already_exists {
                unique_scores.push(scores[i]);
            }
        }
        i = i + 1;
    }
    
    assert(forall|x: int| #[trigger] (unique_scores@.contains(x)) <==> (exists|j: int| 0 <= j < scores.len() && scores@[j] == x && x != 0));
    assert(unique_scores.len() >= 1);
    
    unique_scores.len() as i8
}
// </vc-code>


}

fn main() {}