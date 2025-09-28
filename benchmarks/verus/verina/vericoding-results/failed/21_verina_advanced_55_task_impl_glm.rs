// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn count_occurrences_in_range(xs: Seq<i32>, target: i32, start: int, end: int) -> nat
    requires 0 <= start <= end <= xs.len(),
    ensures count_occurrences_in_range(xs, target, start, end) == xs.subrange(start, end as int).filter(|x: i32| x == target).len()
{
    if start == end {
        0
    } else {
        let count_rest = count_occurrences_in_range(xs, target, start, end - 1);
        if xs[end - 1] == target {
            count_rest + 1
        } else {
            count_rest
        }
    }
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
    let mut max_count = 0;
    let mut result = xs[0];
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            xs@.contains(result),
            max_count == count_occurrences(xs@.subrange(0, i as int), result),
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@.subrange(0, i as int), xs[j]) <= max_count,
            exists|first_idx: int|
                0 <= first_idx < i &&
                xs[first_idx] == result &&
                count_occurrences(xs@.subrange(0, i as int), result) == max_count &&
                forall|k: int| 0 <= k < first_idx ==> count_occurrences(xs@.subrange(0, i as int), xs[k]) < max_count
        decreases xs.len() - i
    {
        let current = xs[i];
        let current_count = count_occurrences(xs@.subrange(0, (i + 1) as int), current);
        
        if current_count > max_count {
            max_count = current_count;
            result = current;
        } else if current_count == max_count {
            // Keep the first occurrence
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}