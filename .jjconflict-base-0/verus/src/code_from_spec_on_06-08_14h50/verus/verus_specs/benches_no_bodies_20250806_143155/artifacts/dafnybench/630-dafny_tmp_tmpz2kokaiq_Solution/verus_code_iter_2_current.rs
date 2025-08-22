use vstd::prelude::*;

verus! {
    spec fn sorted(a: &[int]) -> bool {
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    }

    fn binary_search(a: &[int], x: int) -> (index: i32)
        requires sorted(a),
        ensures 
            (0 <= index < a.len()) ==> a[index as int] == x,
            (index == -1) ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x,
    {
        let mut left: usize = 0;
        let mut right: usize = a.len();
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while left < right
            invariant
                left <= right <= a.len(),
                forall|i: int| 0 <= i < left ==> a[i] < x,
                forall|i: int| right <= i < a.len() ==> a[i] > x,
            decreases right - left
        {
            let mid = left + (right - left) / 2;
            
            if a[mid] == x {
                return mid as i32;
            } else if a[mid] < x {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        
        -1
    }
}

fn main() {}