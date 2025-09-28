// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_occurrences_nonnegative(xs: Seq<i32>, target: i32) 
    ensures count_occurrences(xs, target) >= 0 
{
}

spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

proof fn lemma_max_properties(a: nat, b: nat) 
    ensures max(a, b) >= a && max(a, b) >= b,
            a >= b ==> max(a, b) == a,
            b >= a ==> max(a, b) == b 
{
}

fn count_occurrences_exec(xs: &Vec<i32>, target: i32) -> (result: usize)
    ensures result == count_occurrences(xs@, target) as usize
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count == count_occurrences(xs@.subrange(0, i as int), target) as usize
    {
        if xs[i] == target {
            count += 1;
        }
        i += 1;
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
/* code modified by LLM (iteration 5): fix result variable declaration and ensure spec compatibility */
{
    let mut max_count: usize = 0;
    let mut result: i32 = xs[0];
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant 
            0 <= i <= xs.len(),
            xs@.contains(result),
            max_count == count_occurrences(xs@, result) as usize,
            forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs[j]) as usize <= max_count,
            exists|k: int| 0 <= k < i && xs[k] == result && count_occurrences(xs@, result) as usize == max_count
    {
        let current = xs[i];
        let current_count = count_occurrences_exec(&xs, current);
        
        if current_count > max_count {
            max_count = current_count;
            result = current;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}