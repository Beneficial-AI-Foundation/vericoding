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
fn vec_contains(v: &Vec<i8>, val: i8) -> (res: bool)
    ensures res <==> v@.map(|_, x| x as int).contains(val as int),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j as nat] != val,
    {
        if v[i] == val {
            return true;
        }
        i = i + 1;
    }
    return false;
}

/* helper modified by LLM (iteration 5): fixed compilation error (lemma fn -> proof fn) */
proof fn lemma_exists_implies_unique_non_zero_non_empty(scores: Seq<int>)
    requires
        exists|i: int| 0 <= i < scores.len() && scores[i] != 0,
    ensures
        unique_non_zero_scores(scores).len() >= 1,
{
    let i = choose|i: int| 0 <= i < scores.len() && scores[i] != 0;
    let s = scores[i];
    assert(unique_non_zero_scores(scores).contains(s));
}

/* helper modified by LLM (iteration 5): added lemma to prove result.len <= scores.len */
proof fn lemma_unique_non_zero_len_le_scores_len(scores: Seq<int>)
    ensures unique_non_zero_scores(scores).len() <= scores.len(),
{
    assert forall |x: int| unique_non_zero_scores(scores).contains(x) implies scores.to_set().contains(x) by {
        let i = choose |i: int| 0 <= i < scores.len() && scores[i] != 0 && scores[i] == x;
        assert(scores.to_set().contains(x));
    };
    vstd::set_lib::assert_subset_le(unique_non_zero_scores(scores), scores.to_set());
    vstd::seq_lib::lemma_len_of_to_set_le_len(scores);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): refactored loop and added proof blocks for verification */
{
    let mut unique_scores: Vec<i8> = Vec::new();
    let scores_int = scores@.map(|_, s| s as int);

    let mut i: usize = 0;
    while i < (n as usize)
        invariant
            0 <= i <= n as usize,
            n as int == scores@.len(),
            scores_int == scores@.map(|_, s| s as int),
            forall|k: int| 0 <= k < unique_scores@.len() ==> unique_scores@[k] != 0,
            vstd::seq::unique_elements(unique_scores@.map(|_, s| s as int)),
            unique_scores@.map(|_, s| s as int).to_set() == unique_non_zero_scores(scores_int.subrange(0, i as int)),
        decreases (n as usize) - i
    {
        let current_score = scores[i];
        if current_score != 0 {
            let is_present = vec_contains(&unique_scores, current_score);
            if !is_present {
                let old_unique_scores_int = unique_scores@.map(|_, s| s as int);
                unique_scores.push(current_score);
                proof {
                    let current_score_int = current_score as int;
                    assert(!old_unique_scores_int.contains(current_score_int));
                    vstd::seq_lib::lemma_unique_elements_push(old_unique_scores_int, current_score_int);
                    assert(vstd::seq::unique_elements(unique_scores@.map(|_, s| s as int)));
                }
            }
        }
        i = i + 1;
    }

    proof {
        let scores_int = scores@.map(|_, s| s as int);
        let unique_scores_int = unique_scores@.map(|_, s| s as int);

        vstd::seq_lib::unique_elements_to_set(unique_scores_int);
        assert(unique_scores.len() as int == unique_scores_int.to_set().len());

        assert(unique_scores_int.to_set() == unique_non_zero_scores(scores_int));

        assert(unique_scores.len() as int == unique_non_zero_scores(scores_int).len());

        lemma_exists_implies_unique_non_zero_non_empty(scores_int);
        lemma_unique_non_zero_len_le_scores_len(scores_int);
    }
    
    return unique_scores.len() as i8;
}
// </vc-code>


}

fn main() {}