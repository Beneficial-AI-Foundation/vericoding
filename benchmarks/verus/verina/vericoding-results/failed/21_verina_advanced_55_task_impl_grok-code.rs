// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
fn count_occurrences_exec(xs: &Vec<i32>, target: i32) -> (count: usize) {
    let mut cnt = 0;
    let mut i = 0;
    while i < xs.len() 
        invariant i <= xs.len(),
            cnt == count_occurrences(xs@.take(i as int), target) as usize,
    {
        if xs[i] == target {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

proof fn count_exec_matches_spec(xs: &Vec<i32>, target: i32)
    ensures count_occurrences(xs@, target) as usize == count_occurrences_exec(xs, target),
{
    assert(count_occurrences(xs@.take(xs.len() as int), target) == count_occurrences(xs@, target));
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
    /* code modified by LLM (iteration 2): fixed syntax for exists quantification and adjusted proof block to ensure postconditions */
    let max_count_init = count_occurrences_exec(&xs, xs[0]);
    let mut max_count = max_count_init;
    let mut result = xs[0];
    let mut first = 0usize;
    let mut i = 1;
    while i < xs.len() 
        invariant 0 <= i <= xs.len(),
            xs@.contains(result),
            xs@.take(i as int).filter(|x: i32| x == xs[first]).len() == max_count as nat,
            forall |j: int| 0 <= j < i ==> count_occurrences(xs@.take(i as int), xs[j]) <= max_count as nat,
    {
        let cnt = count_occurrences_exec(&xs, xs[i]);
        if cnt > max_count {
            max_count = cnt;
            result = xs[i];
            first = i;
        }
        i += 1;
    }
    assert(i == xs.len());
    proof {
        assert(count_occurrences(xs@, result) == max_count as nat);
        assert forall |x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result) by {
        };
        assert exists |first_idx: int| (0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall |j: int| 0 <= j < first_idx ==> count_occurrences(xs@, xs[j]) < count_occurrences(xs@, result));
    }
    result
}
// </vc-code>

}
fn main() {}