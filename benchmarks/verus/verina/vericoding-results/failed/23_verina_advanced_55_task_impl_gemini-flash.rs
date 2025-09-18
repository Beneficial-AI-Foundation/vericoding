// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed any helper to simplify the code */
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
/* code modified by LLM (iteration 5): Fix compilation error related to casting `xs.len()` to `int` inside the loop condition. Cast only when using in `i` definition. */
{
    let mut max_count: nat = 0;
    let mut most_freq_val: i32 = xs[0];

    let mut i: int = 0;
    while (i as usize) < xs.len()
        invariant
            0 <= i <= xs.len() as int,
            max_count == count_occurrences(xs@, most_freq_val),
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs[j as usize]) <= max_count,
            xs.len() > 0 ==> xs@.contains(most_freq_val),
    {
        let current_val = xs[i as usize];
        let current_count = count_occurrences(xs@, current_val);

        if current_count > max_count {
            max_count = current_count;
            most_freq_val = current_val;
        }

        i = i + 1;
    }
    most_freq_val
}
// </vc-code>

}
fn main() {}