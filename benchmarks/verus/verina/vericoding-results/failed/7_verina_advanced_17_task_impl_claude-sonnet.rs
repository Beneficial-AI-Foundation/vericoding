// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to track element positioning during insertion */
spec fn is_sorted_up_to(v: Vec<i32>, end: int) -> bool {
    forall|k1: int, k2: int| 0 <= k1 < k2 < end ==> v[k1] <= v[k2]
}

spec fn valid_index(v: Vec<i32>, i: int) -> bool {
    0 <= i < v.len()
}

spec fn elements_shifted_correctly(v: Vec<i32>, start: int, end: int, key: i32) -> bool {
    forall|k: int| start <= k < end ==> v[k] > key
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant violations by starting from 0 and correcting multiset preservation */
    let mut sorted = l;
    let mut i = 0;
    
    while i < sorted.len()
        invariant
            0 <= i <= sorted.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> sorted[k1] <= sorted[k2],
            sorted@.to_multiset() == l@.to_multiset(),
        decreases sorted.len() - i
    {
        if i > 0 {
            let key = sorted[i];
            let mut j = i;
            
            while j > 0 && sorted[j - 1] > key
                invariant
                    0 <= j <= i < sorted.len(),
                    forall|k1: int, k2: int| 0 <= k1 < k2 < j ==> sorted[k1] <= sorted[k2],
                    forall|k1: int, k2: int| j < k1 < k2 <= i ==> sorted[k1] <= sorted[k2],
                    forall|k: int| j <= k < i ==> sorted[k] == sorted@[k + 1],
                    sorted@.to_multiset() == l@.to_multiset(),
                decreases j
            {
                sorted.set(j, sorted[j - 1]);
                j = j - 1;
            }
            
            sorted.set(j, key);
        }
        i = i + 1;
    }
    
    sorted
}
// </vc-code>

}
fn main() {}