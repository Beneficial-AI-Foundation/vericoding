//This example is from Verus tutorial, Chpt 7.5
use vstd::prelude::*;
fn main() {}

verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut low: usize = 0;
    let mut high: usize = v.len() - 1;
    
    while low <= high
        invariant
            low <= high + 1,
            high < v.len(),
            forall|i:int| 0 <= i < low ==> v[i] < k,
            forall|i:int| high < i < v.len() ==> v[i] > k,
            exists|i:int| low <= i <= high && k == v[i],
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            /* code modified by LLM (iteration 2): removed incorrect assertion - we only know v[mid] < k, not all elements up to mid */
            low = mid + 1;
        } else {
            /* code modified by LLM (iteration 2): fixed the logic - if v[mid] > k, we should search in the lower half */
            if mid == 0 {
                /* code modified by LLM (iteration 2): this case is impossible given our preconditions - if mid == 0 and v[0] > k, but k exists in the array, we have a contradiction */
                assert(false);
            }
            /* code modified by LLM (iteration 2): removed incorrect assertion - we only know v[mid] > k, not all elements from mid onwards */
            high = mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 2): this point should be unreachable given the loop invariants and preconditions */
    assert(false);
    0
}
}