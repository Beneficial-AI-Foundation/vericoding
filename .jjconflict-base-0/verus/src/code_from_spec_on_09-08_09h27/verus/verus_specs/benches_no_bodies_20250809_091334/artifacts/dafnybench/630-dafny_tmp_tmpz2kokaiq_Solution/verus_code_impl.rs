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
        if a.len() == 0 {
            return -1;
        }
        
        let mut left: usize = 0;
        let mut right: usize = a.len() - 1;
        
        /* code modified by LLM (iteration 1): Added decreases clause and fixed loop condition to handle usize underflow */
        while left <= right && right < a.len()
            invariant
                left <= a.len(),
                right < a.len() || right == usize::MAX,
                forall|i: int| 0 <= i < left ==> a[i] < x,
                forall|i: int| right < i < a.len() && right != usize::MAX ==> a[i] > x,
            decreases right - left
        {
            let mid = left + (right - left) / 2;
            
            if a[mid] == x {
                return mid as i32;
            } else if a[mid] < x {
                /* code modified by LLM (iteration 1): Fixed potential infinite loop when mid is at the end */
                if mid == a.len() - 1 {
                    break;
                }
                left = mid + 1;
            } else {
                /* code modified by LLM (iteration 1): Handle usize underflow by setting to MAX value */
                if mid == 0 {
                    right = usize::MAX;
                    break;
                } else {
                    right = mid - 1;
                }
            }
        }
        
        -1
    }
}

fn main() {}