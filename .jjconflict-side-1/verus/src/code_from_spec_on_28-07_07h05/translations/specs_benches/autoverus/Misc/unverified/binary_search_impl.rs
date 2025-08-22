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
    let mut left: usize = 0;
    let mut right: usize = v.len();
    
    /* code modified by LLM (iteration 3): fixed loop invariants to use strict inequalities for elements not equal to k */
    while left < right
        invariant
            left <= right <= v.len(),
            forall|i:int| 0 <= i < left ==> v[i] < k,
            forall|i:int| right <= i < v.len() ==> v[i] > k,
            exists|i:int| left <= i < right && k == v[i],
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        /* code modified by LLM (iteration 3): added assertions with proper type casting from usize to int */
        assert(left <= mid < right);
        assert(0 <= mid < v.len());
        
        if v[mid as int] < k {
            /* code modified by LLM (iteration 3): added assertion with proper type casting to prove left invariant preservation */
            assert(forall|i:int| 0 <= i <= mid as int ==> v[i] < k);
            left = mid + 1;
        } else if v[mid as int] > k {
            /* code modified by LLM (iteration 3): added assertion with proper type casting to prove right invariant preservation */
            assert(forall|i:int| mid as int <= i < v.len() ==> v[i] > k);
            right = mid;
        } else {
            /* code modified by LLM (iteration 3): added assertion with proper type casting to verify we found the target */
            assert(v[mid as int] == k);
            return mid;
        }
    }
    
    // This point should never be reached due to the precondition
    // that guarantees the key exists, but we need to satisfy the compiler
    0
}
}