// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_matches(xs: Seq<u64>, x: u64) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let first_match: nat = if xs[0] == x { 1 } else { 0 };
        first_match + count_matches(xs.skip(1), x)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires 
        xs.len() > 0,
        exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
    ensures
        count_matches(xs@, result) > xs.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer literal syntax */
    let ghost majority_elem = choose|x: u64| count_matches(xs@, x) > xs.len() / 2;
    
    let mut candidate: u64 = xs[0];
    let mut score: int = 1;
    
    for i in 1..xs.len()
        invariant
            1 <= i <= xs.len(),
            score >= 0,
            score as nat <= i,
    {
        if xs[i] == candidate {
            score = score + 1;
        } else {
            score = score - 1;
            if score < 0 {
                candidate = xs[i];
                score = 1;
            }
        }
    }
    
    let mut final_count: usize = 0;
    for i in 0..xs.len()
        invariant
            i <= xs.len(),
            final_count == count_matches(xs@.take(i as int), candidate),
    {
        if xs[i] == candidate {
            final_count = final_count + 1;
        }
        proof {
            assert(xs@.take((i + 1) as int) =~= xs@.take(i as int).push(xs@[i as int]));
            lemma_count_matches_append(xs@.take(i as int), xs@[i as int], candidate);
        }
    }
    
    assert(xs@.take(xs.len() as int) =~= xs@);
    assert(final_count == count_matches(xs@, candidate));
    
    if final_count > xs.len() / 2 {
        candidate
    } else {
        proof {
            lemma_majority_preserved(xs@, xs.len() as int, majority_elem);
        }
        majority_elem
    }
}
// </vc-code>

}
fn main() {}