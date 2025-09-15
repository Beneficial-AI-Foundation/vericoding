// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type mismatch by using int indexing */
fn count_in_vec(xs: &Vec<i32>, target: i32) -> (count: usize)
    ensures count == count_occurrences(xs@, target)
{
    let mut count = 0;
    for i in 0..xs.len()
        invariant
            count == count_occurrences(xs@.subrange(0, i as int), target)
    {
        if xs[i] == target {
            count = count + 1;
        }
        proof {
            assert(xs@.subrange(0, (i + 1) as int) == xs@.subrange(0, i as int).push(xs@[i as int]));
        }
    }
    proof {
        assert(xs@.subrange(0, xs.len() as int) == xs@);
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
    /* code modified by LLM (iteration 5): Fix invariant maintenance and assertions */
    let mut most_freq = xs[0];
    let mut max_count = count_in_vec(&xs, xs[0]);
    let mut first_idx = 0;
    
    for i in 1..xs.len()
        invariant
            xs.len() > 0,
            0 <= first_idx < xs.len(),
            xs@.contains(most_freq),
            xs@[first_idx as int] == most_freq,
            max_count == count_occurrences(xs@, most_freq),
            forall|j: int| 0 <= j < first_idx ==> count_occurrences(xs@, xs@[j]) < max_count,
            forall|x: i32| xs@.subrange(0, i as int).contains(x) ==> count_occurrences(xs@, x) <= max_count,
            first_idx < i,
    {
        let current = xs[i];
        let current_count = count_in_vec(&xs, current);
        
        if current_count > max_count {
            most_freq = current;
            max_count = current_count;
            first_idx = i;
        }
        
        proof {
            assert(xs@.subrange(0, (i + 1) as int) =~= xs@.subrange(0, i as int).push(xs@[i as int]));
            assert(xs@.subrange(0, (i + 1) as int).contains(current));
            
            if current_count > max_count {
                // When we update, first_idx becomes i, so condition holds
                assert(forall|j: int| 0 <= j < i ==> count_occurrences(xs@, xs@[j]) <= max_count);
            } else {
                // When we don't update, first_idx stays the same and < i
                assert(first_idx < i);
            }
        }
    }
    
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
        assert(forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= max_count);
        assert(exists|idx: int| idx == first_idx as int && 
               0 <= idx < xs.len() && 
               xs@[idx] == most_freq && 
               count_occurrences(xs@, most_freq) == count_occurrences(xs@, xs@[idx]) &&
               forall|j: int| 0 <= j < idx ==> count_occurrences(xs@, xs@[j]) < count_occurrences(xs@, most_freq)) by {
            assert(count_occurrences(xs@, most_freq) == max_count);
            assert(count_occurrences(xs@, xs@[first_idx as int]) == max_count);
        }
    }
    
    most_freq
}
// </vc-code>

}
fn main() {}