// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min_spec(seq: Seq<i32>) -> (result: int)
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed attribute for min function to use separate spec and exec attributes */
    #[verifier::spec]
    #[verifier::exec]
    fn min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    proof fn lemma_min_spec_drop_first_invariant(seq: Seq<i32>)
        requires 1 <= seq.len(),
        ensures min_spec(seq) == min(seq[0] as int, min_spec(seq.drop_first())),
        decreases seq.len()
    {
        if seq.len() == 1 {
            assert(seq.drop_first().len() == 0);
            assert(min_spec(seq.drop_first()) == 0);
        } else {
            lemma_min_spec_drop_first_invariant(seq.drop_first());
        }
    }
// </vc-helpers>

// <vc-spec>
fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))

    requires
        numbers.len() >= 2,

    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes to implementation */
{
    let mut min_idx: usize = 0;
    let mut second_min_idx: usize = 1;
    
    if numbers[min_idx] > numbers[second_min_idx] {
        min_idx = 1;
        second_min_idx = 0;
    }
    
    let mut i = 2;
    while i < numbers.len()
        invariant
            forall|k: int| 0 <= k < i as int && k != (min_idx as int) ==> numbers@[k] >= numbers@[second_min_idx as int],
            forall|k: int| 0 <= k < i as int ==> numbers@[k] >= numbers@[min_idx as int],
            0 <= min_idx < i,
            0 <= second_min_idx < i,
            min_idx != second_min_idx,
    {
        if numbers[i] < numbers[min_idx] {
            second_min_idx = min_idx;
            min_idx = i;
        } else if numbers[i] < numbers[second_min_idx] && i != min_idx {
            second_min_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_min_spec_drop_first_invariant(numbers@);
    }
    
    (min_idx, second_min_idx)
}
// </vc-code>

}
fn main() {}