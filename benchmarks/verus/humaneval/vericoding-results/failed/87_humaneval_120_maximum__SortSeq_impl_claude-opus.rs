// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: &Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> #[trigger] sorted@[i] <= #[trigger] sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] s@[i] == #[trigger] sorted@[j],
        forall|x: i8| #[trigger] s@.contains(x) ==> #[trigger] sorted@.contains(x),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] sorted@[i] == #[trigger] s@[j],
        forall|x: i8| #[trigger] sorted@.contains(x) ==> #[trigger] s@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Strengthened invariants to maintain multiset equality */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted@.len() == n,
            sorted@.len() == s@.len(),
            sorted@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i as int ==> #[trigger] sorted@[k] <= #[trigger] sorted@[l],
            forall|k: int| 0 <= k < i as int ==> forall|l: int| i as int <= l < n ==> #[trigger] sorted@[k] <= #[trigger] sorted@[l],
            forall|idx: int| 0 <= idx < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && s@[idx] == sorted@[j],
            forall|idx: int| 0 <= idx < sorted@.len() ==> exists|j: int| 0 <= j < s@.len() && sorted@[idx] == s@[j],
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                0 <= i < n,
                i + 1 <= j <= n,
                i <= min_idx < n,
                min_idx < j,
                sorted@.len() == n,
                sorted@.len() == s@.len(),
                sorted@.to_multiset() == s@.to_multiset(),
                forall|k: int| i as int <= k < j as int ==> sorted@[min_idx as int] <= sorted@[k],
                forall|k: int, l: int| 0 <= k < l < i as int ==> #[trigger] sorted@[k] <= #[trigger] sorted@[l],
                forall|k: int| 0 <= k < i as int ==> forall|l: int| i as int <= l < n ==> #[trigger] sorted@[k] <= #[trigger] sorted@[l],
                forall|idx: int| 0 <= idx < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && s@[idx] == sorted@[j],
                forall|idx: int| 0 <= idx < sorted@.len() ==> exists|j: int| 0 <= j < s@.len() && sorted@[idx] == s@[j],
            decreases n - j
        {
            if j < n && min_idx < n && sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i && i < n && min_idx < n {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}