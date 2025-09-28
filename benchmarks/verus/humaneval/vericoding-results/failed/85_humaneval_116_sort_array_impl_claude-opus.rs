// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_array(s: Vec<u8>) -> (sorted: Vec<u8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> popcount(sorted@[i] as nat) <= popcount(sorted@[j] as nat)
            && sorted@.len() == s@.len()
            && s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clause to inner popcount_exec loop */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    // Helper function to compute popcount at runtime
    let popcount_exec = |x: u8| -> u8 {
        let mut count: u8 = 0;
        let mut val = x;
        while val > 0
            decreases val
        {
            count = count + (val & 1);
            val = val >> 1;
        }
        count
    };
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted@.len() == s@.len(),
            sorted@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l <= i ==> popcount(sorted@[k] as nat) <= popcount(sorted@[l] as nat),
            forall|k: int| 0 <= k < i ==> forall|l: int| i <= l < sorted@.len() ==> popcount(sorted@[k] as nat) <= popcount(sorted@[l] as nat),
            i <= n,
            n == sorted.len(),
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                i < n,
                i + 1 <= j <= n,
                i <= min_idx < n,
                n == sorted.len(),
                sorted@.len() == s@.len(),
                sorted@.to_multiset() == s@.to_multiset(),
                forall|k: int| i <= k < j ==> popcount(sorted@[min_idx as int] as nat) <= popcount(sorted@[k] as nat),
                forall|k: int, l: int| 0 <= k < l <= i ==> popcount(sorted@[k] as nat) <= popcount(sorted@[l] as nat),
                forall|k: int| 0 <= k < i ==> forall|l: int| i <= l < sorted@.len() ==> popcount(sorted@[k] as nat) <= popcount(sorted@[l] as nat),
            decreases n - j
        {
            if popcount_exec(sorted[j]) < popcount_exec(sorted[min_idx]) {
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
    
    sorted
}
// </vc-code>


}

fn main() {}