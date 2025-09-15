// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>

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
    let mut max_count: usize = 0;
    let mut result = xs[0];
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            xs.len() > 0,
            xs@.contains(result),
            max_count == count_occurrences(xs@, result) as usize,
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs[j]) <= max_count as nat,
            exists|first_idx: int|
                0 <= first_idx < xs.len() &&
                xs[first_idx] == result &&
                forall|k: int| 0 <= k < first_idx ==> count_occurrences(xs@, xs[k]) < count_occurrences(xs@, result),
    {
        let current = xs[i];
        let mut count: usize = 0;
        let mut j: usize = 0;
        
        while j < xs.len()
            invariant
                0 <= j <= xs.len(),
                count == count_occurrences(xs@.take(j as int), current) as usize,
        {
            if xs[j] == current {
                count = count + 1;
            }
            j = j + 1;
        }
        
        assert(xs@.take(xs.len() as int) =~= xs@);
        assert(count == count_occurrences(xs@, current) as usize);
        
        if count > max_count {
            max_count = count;
            result = current;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}