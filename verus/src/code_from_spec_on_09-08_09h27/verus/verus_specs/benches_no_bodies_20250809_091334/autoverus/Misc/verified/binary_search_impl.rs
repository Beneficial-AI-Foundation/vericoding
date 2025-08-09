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
    
    /* code modified by LLM (iteration 1): Added decreases clause to fix loop verification error */
    loop
        invariant
            low <= high,
            high < v.len(),
            exists|i:int| low <= i <= high && k == v[i],
            forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
}
}