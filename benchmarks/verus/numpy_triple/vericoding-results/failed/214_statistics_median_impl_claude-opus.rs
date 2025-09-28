// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

fn median(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|sorted: Seq<int>| #[trigger] sorted.len() == a@.len() &&
            is_sorted(sorted) &&
            (if a.len() % 2 == 1 {
                result as int == sorted[((a.len() - 1) / 2) as int]
            } else {
                result as int == (sorted[(a.len() / 2 - 1) as int] + sorted[(a.len() / 2) as int]) / 2
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotation for quantifier */
    let mut sorted = a.clone();
    let n = sorted.len();
    
    let mut i = 0;
    while i < n
        invariant
            sorted.len() == n,
            n == a.len(),
            n > 0,
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < l < i ==> sorted@[k] <= sorted@[l],
            forall|k: int| #[trigger] sorted@[k], 0 <= k < n ==> 
                exists|l: int| 0 <= l < n && sorted@[k] == a@[l],
        decreases n - i
    {
        let mut j = i + 1;
        let mut min_idx = i;
        
        while j < n
            invariant
                sorted.len() == n,
                n == a.len(),
                n > 0,
                i < n,
                i + 1 <= j <= n,
                i <= min_idx < n,
                forall|k: int| i <= k < j ==> sorted@[min_idx as int] <= sorted@[k],
                forall|k: int, l: int| 0 <= k < l < i ==> sorted@[k] <= sorted@[l],
                forall|k: int| #[trigger] sorted@[k], 0 <= k < n ==> 
                    exists|l: int| 0 <= l < n && sorted@[k] == a@[l],
            decreases n - j
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    proof {
        let sorted_as_ints: Seq<int> = Seq::new(sorted@.len(), |k: int| sorted@[k] as int);
        assert(forall|k: int, l: int| 0 <= k < l < sorted_as_ints.len() ==> sorted_as_ints[k] <= sorted_as_ints[l]);
        assert(is_sorted(sorted_as_ints));
    }
    
    if n % 2 == 1 {
        let mid = (n - 1) / 2;
        sorted[mid]
    } else {
        let mid1 = n / 2 - 1;
        let mid2 = n / 2;
        let sum = sorted[mid1] as i32 + sorted[mid2] as i32;
        (sum / 2) as i8
    }
}
// </vc-code>


}
fn main() {}