// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): none needed */
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
    /* code modified by LLM (iteration 5): Changed all `int` type declarations to `u64` where it is used to represent an executable count value rather than a ghost integer. This specifically applies to `max_count` and `current_count` to resolve errors about `nat` and `int` being ghost-only types. The initial value of `max_count` is set to the occurrences of the first element of `xs` which is then converted to `u64` to match the type of `max_count`. */
    let mut max_count: u64 = count_occurrences(xs@, xs[0]) as u64;
    let mut most_frequent_element = xs[0];

    let mut i = 0;
    while i < xs.len()
        invariant
            0 <= i as int <= xs.len() as int,
            xs.len() > 0,
            max_count == count_occurrences(xs@, most_frequent_element) as u64,
            // All elements processed so far have a count less than or equal to max_count in specification.
            forall|j: int| 0 <= j < i ==> (count_occurrences(xs@, xs[j]) as u64) <= max_count
        decreases (xs.len() - i) as int
    {
        let current_element = xs[i];
        let current_count: u64 = count_occurrences(xs@, current_element) as u64;

        if current_count > max_count {
            max_count = current_count;
            most_frequent_element = current_element;
        }
        i = i + 1;
    }
    most_frequent_element
}
// </vc-code>

}
fn main() {}