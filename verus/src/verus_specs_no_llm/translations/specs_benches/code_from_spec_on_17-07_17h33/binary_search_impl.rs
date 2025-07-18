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
    let mut left: usize = 0;
    let mut right: usize = v.len() - 1;
    
    /* code modified by LLM (iteration 4): fixed invariants and loop condition to handle underflow and maintain existence invariant */
    loop
        invariant
            left <= v.len(),
            right < v.len(),
            exists|i: int| 0 <= i < v.len() && k == v[i],
            forall|i: int| 0 <= i < left ==> v[i] < k,
            forall|i: int| right < i < v.len() ==> v[i] > k,
        decreases 
            if left <= right { right + 1 - left } else { 0 }
    {
        if left > right {
            /* code modified by LLM (iteration 4): this case should not occur due to precondition, but we need to handle it */
            // Due to the precondition, there must exist an element equal to k
            // Since we've eliminated all possibilities, this is unreachable
            assert(false);
        }
        
        let mid = left + (right - left) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            left = mid + 1;
        } else {
            /* code modified by LLM (iteration 4): handle potential underflow by checking if mid is 0 */
            if mid == 0 {
                // If mid is 0 and v[mid] > k, then k cannot exist in the array
                // But this contradicts our precondition
                assert(false);
            } else {
                right = mid - 1;
            }
        }
    }
}

} // verus!