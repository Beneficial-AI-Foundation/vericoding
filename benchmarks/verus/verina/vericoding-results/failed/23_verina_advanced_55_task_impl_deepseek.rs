// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_to_nat_conversion(count: nat) -> (result: int)
    ensures result == count as int
{
    /* helper modified by LLM (iteration 5): Fixed variable declaration */
    let result = count as int;
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
    /* code modified by LLM (iteration 5): Fixed variable declarations and conversion */
    let mut max_count = 0;
    let mut result = xs[0];
    let mut idx = 0;
    
    while idx < xs.len()
        invariant
            0 <= idx <= xs.len(),
            xs@.contains(result),
            count_occurrences(xs@, result) as int == max_count,
            forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) as int <= max_count,
            exists|first_idx: int| 
                0 <= first_idx < xs.len() && 
                xs[first_idx] == result && 
                count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
                forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result)
    {
        let current = xs[idx];
        let current_count = count_occurrences(xs@, current);
        let current_count_int: int;
        proof {
            current_count_int = lemma_count_to_nat_conversion(current_count);
        }
        
        if current_count_int > max_count {
            max_count = current_count_int;
            result = current;
            proof {
                lemma_first_occurrence_exists(xs@, current);
            }
        }
        
        idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}