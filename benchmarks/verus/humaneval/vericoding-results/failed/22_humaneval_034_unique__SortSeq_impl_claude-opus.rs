// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type error by casting i to int in index access */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted@.len() == s@.len(),
            sorted@.len() == n,
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i ==> sorted@[k] <= sorted@[l],
            forall|k: int| 0 <= k < i && i < n ==> sorted@[k] <= sorted@[i as int],
            i <= n,
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                i < n,
                i + 1 <= j <= n,
                i <= min_idx < n,
                sorted@.len() == n,
                forall|k: int| i <= k < j ==> sorted@[min_idx as int] <= sorted@[k],
            decreases n - j
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let old_sorted = sorted.clone();
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
            
            proof {
                assert(sorted@.to_multiset() == old_sorted@.to_multiset());
                assert(sorted@[i as int] == old_sorted@[min_idx as int]);
                assert(sorted@[min_idx as int] == old_sorted@[i as int]);
                assert(forall|k: int| i < k < n ==> old_sorted@[min_idx as int] <= old_sorted@[k]);
                assert(forall|k: int| 0 <= k < i ==> old_sorted@[k] <= old_sorted@[min_idx as int]);
            }
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}