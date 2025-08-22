use vstd::prelude::*;

fn main() {}
verus! {

fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut left: usize = 0;
    let mut right: usize = v.len();
    
    while left < right
        invariant
            left <= right <= v.len(),
            exists|i: int| left <= i < right && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        let mid = left + (right - left) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    // This should never be reached due to the precondition that k exists
    unreachable!()
}

} // verus!