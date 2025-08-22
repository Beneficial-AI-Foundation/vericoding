use vstd::prelude::*;

verus! {
    #[verifier::loop_isolation(false)]
    fn binary_search(a: &[int], key: int) -> (n: usize)
        requires 
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        ensures 
            0 <= n <= a.len(),
            forall|i: int| 0 <= i < n ==> a[i] < key,
            n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
            forall|i: int| n <= i < a.len() ==> a[i] >= key,
    {
        let mut left: usize = 0;
        let mut right: usize = a.len();
        
        while left < right
            invariant
                0 <= left <= right <= a.len(),
                forall|i: int| 0 <= i < left ==> a[i] < key,
                forall|i: int| right <= i < a.len() ==> a[i] >= key,
        {
            let mid = left + (right - left) / 2;
            
            if a[mid] < key {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        
        left
    }
}

fn main() {}