// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Changed return type to usize and adjusted postcondition */
fn count_occurrences_exec(xs: &Vec<i32>, target: i32) -> (count: usize)
    ensures count as nat == count_occurrences(xs@, target)
{
    let mut count: usize = 0;
    for i in 0..xs.len()
        invariant count as nat == count_occurrences(xs@.subrange(0, i as int), target)
    {
        if xs[i] == target {
            count += 1;
        }
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
/* code modified by LLM (iteration 3): Fixed nat/int usage by changing types and adding conversions */
{
    let mut max_count: usize = 0;
    let mut result = xs[0];
    let mut first_idx: usize = 0;
    max_count = count_occurrences_exec(&xs, xs[0]);
    for i in 1..xs.len()
        invariant
            1 <= i <= xs.len(),
            xs@.contains(result),
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) <= max_count as nat,
            max_count as nat == count_occurrences(xs@, result),
            0 <= first_idx as int < xs.len(),
            xs@[first_idx as int] == result,
            forall|j: int| 0 <= j < first_idx as int ==> count_occurrences(xs@, xs@[j]) < max_count as nat,
    {
        let count_i = count_occurrences_exec(&xs, xs[i]);
        if count_i > max_count {
            max_count = count_i;
            result = xs[i];
            first_idx = i;
        }
    }
    result
}
// </vc-code>

}
fn main() {}