// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases clauses and strengthen invariants */
proof fn max_rcur_same_as_last_when_len_1(seq: Seq<i32>) requires seq.len() == 1, ensures max_rcur(seq) == seq[0] as int {}
proof fn min_rcur_same_as_last_when_len_1(seq: Seq<i32>) requires seq.len() == 1, ensures min_rcur(seq) == seq[0] as int {}
proof fn max_rcur_recursive_lemma(seq: Seq<i32>) 
    requires seq.len() > 1, 
    ensures max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())) 
    decreases seq.len()
{}
proof fn min_rcur_recursive_lemma(seq: Seq<i32>) 
    requires seq.len() > 1, 
    ensures min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())) 
    decreases seq.len()
{}
proof fn max_property_lemma(a: int, b: int) ensures max(a, b) >= a && max(a, b) >= b {}
proof fn min_property_lemma(a: int, b: int) ensures min(a, b) <= a && min(a, b) <= b {}
proof fn seq_subrange_invariant_lemma(arr: Seq<i32>, i: int) 
    requires 0 <= i <= arr.len(), 
    ensures arr.subrange(0, i).len() == i {
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add decreases clause to loop and fix verification */
{
    let mut current_max = arr[0];
    let mut current_min = arr[0];
    let mut sum_so_far = 0;
    
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            current_max == max_rcur(arr@.subrange(0, i as int)),
            current_min == min_rcur(arr@.subrange(0, i as int)),
            sum_so_far == max_rcur(arr@.subrange(0, i as int)) + min_rcur(arr@.subrange(0, i as int)),
            forall|j: int| 0 <= j < i as int ==> current_min <= #[trigger] arr[j] <= current_max,
        decreases arr.len() - i
    {
        let elem = arr[i];
        
        proof {
            seq_subrange_invariant_lemma(arr@, i as int + 1);
            max_rcur_recursive_lemma(arr@.subrange(0, i as int + 1));
            min_rcur_recursive_lemma(arr@.subrange(0, i as int + 1));
        }
        
        current_max = if elem > current_max { elem } else { current_max };
        current_min = if elem < current_min { elem } else { current_min };
        
        proof {
            assert(current_max == max_rcur(arr@.subrange(0, i as int + 1)));
            assert(current_min == min_rcur(arr@.subrange(0, i as int + 1)));
        }
        
        sum_so_far = current_max + current_min;
        i += 1;
    }
    
    sum_so_far
}
// </vc-code>

}
fn main() {}