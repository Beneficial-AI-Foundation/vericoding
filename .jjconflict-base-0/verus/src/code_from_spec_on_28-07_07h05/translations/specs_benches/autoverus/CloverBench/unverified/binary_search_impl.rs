use vstd::prelude::*;

fn main() {}
verus! {

//IMPL binary_search
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut low: usize = 0;
    let mut high: usize = v.len() - 1;
    
    /* code modified by LLM (iteration 3): fixed loop invariants and logic to properly maintain bounds and handle edge cases */
    while low <= high
        invariant
            low <= v.len(),
            high < v.len(),
            exists|i: int| 0 <= i < v.len() && k == v[i],
            forall|i: int| 0 <= i < low ==> v[i] < k,
            forall|i: int| high < i < v.len() ==> v[i] > k,
            low <= high + 1,
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            /* code modified by LLM (iteration 3): added assertion to help prove invariant maintenance */
            assert(forall|i: int| 0 <= i <= mid ==> v[i] <= v[mid]);
            assert(forall|i: int| 0 <= i <= mid ==> v[i] < k);
            low = mid + 1;
        } else {
            /* code modified by LLM (iteration 3): added assertion to help prove invariant maintenance and removed unreachable case */
            assert(v[mid] > k);
            assert(forall|i: int| mid <= i < v.len() ==> v[mid] <= v[i]);
            assert(forall|i: int| mid <= i < v.len() ==> v[i] > k);
            if mid == 0 {
                // If mid is 0 and v[0] > k, then there's no valid index less than 0
                // But we know k exists somewhere, so this creates a contradiction
                // However, we need to handle the underflow case properly
                break;
            } else {
                high = mid - 1;
            }
        }
    }
    
    /* code modified by LLM (iteration 3): fixed type conversion issue by removing ghost type usage in executable code */
    // When we reach here, either:
    // 1. We broke out of the loop because mid == 0 and v[0] > k
    // 2. The loop condition low <= high became false
    
    // In case 1, we know k exists and v[0] > k, which means k must be at index 0
    // (since there's nowhere else it can be and we have the existence guarantee)
    if low > high {
        // The loop exited normally, but we know k exists somewhere
        // Given our invariants, k must be in the remaining range
        assert(exists|i: int| 0 <= i < v.len() && k == v[i]);
        // Since we've eliminated all other possibilities, k must be at an index
        // that satisfies both low <= i and i <= high, but low > high
        // This means our search was incomplete - let's check the boundary
        if low < v.len() && v[low] == k {
            return low;
        }
    }
    
    // If we reach here, check if k is at index 0 (the edge case)
    if v[0] == k {
        return 0;
    }
    
    // This should truly be unreachable given our preconditions
    assert(false);
    0
}

} // verus!