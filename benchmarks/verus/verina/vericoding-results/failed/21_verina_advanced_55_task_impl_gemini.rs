// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no logic changes] */
fn count_occurrences_exec(xs: &Vec<i32>, target: i32) -> (count: usize)
    ensures
        count as nat == count_occurrences(xs@, target),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count as nat == count_occurrences(xs@.subrange(0, i as int), target),
    {
        if xs[i] == target {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed compilation error and added proof for ensures clause] */
    let mut result = xs[0];
    let mut max_count = count_occurrences_exec(&xs, result);
    let ghost mut result_idx: int = 0;

    let mut i: usize = 1;
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            0 <= result_idx < i as int,
            result == xs[result_idx],
            max_count as nat == count_occurrences(xs@, result),
            forall|j: int| 0 <= j < i as int ==> count_occurrences(xs@, xs[j]) <= max_count as nat,
            forall|j: int| 0 <= j < result_idx ==> count_occurrences(xs@, xs[j]) < max_count as nat,
    {
        let current_val = xs[i];
        let current_count = count_occurrences_exec(&xs, current_val);

        if current_count > max_count {
            result = current_val;
            max_count = current_count;
            proof { result_idx = i as int; }
        }
        i = i + 1;
    }
    
    proof {
        assert forall|x: i32| xs@.contains(x) implies count_occurrences(xs@, x) <= count_occurrences(xs@, result) by {
            let k = vstd::seq_lib::lemma_seq_contains_witness(xs@, x);
            assert(count_occurrences(xs@, xs[k]) <= max_count as nat);
        }

        assert(exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result));
    }

    result
}
// </vc-code>

}
fn main() {}