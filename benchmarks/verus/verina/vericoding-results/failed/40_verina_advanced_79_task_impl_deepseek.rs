// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed deprecated methods and type mismatches */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn option_unwrap_some<T>(opt: Option<T>) -> T 
    requires opt.is_Some() 
{ 
    opt.get_Some_0() 
}
proof fn lemma_vec_len_index_bound(v: Vec<i32>, i: int) 
    requires 0 <= i < v.len() 
{}
proof fn lemma_vec_len_index_bound_usize(v: Vec<i32>, i: usize) 
    requires i < v.len() 
{}
proof fn lemma_forall_negation_exists(v: Vec<i32>, target: i32) 
    ensures 
        (forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> v[i] + v[j] != target) ==
        !(exists|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j && v[i] + v[j] == target) 
{}
proof fn lemma_ordered_pair_exists_search(v: Vec<i32>, target: i32, i: usize, j: usize, n: usize) 
    requires 
        i < j < n,
        v[i] + v[j] == target
    ensures 
        !(forall|k1: int, k2: int| 0 <= k1 < n && 0 <= k2 < n && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> v[k1] + v[k2] != target) 
{}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Vec<i32>, target: i32) -> (result: Option<(usize, usize)>)
    ensures
        match result {
            None => {
                forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target
            },
            Some((i, j)) => {
                i < j &&
                j < nums.len() &&
                nums[i as int] + nums[j as int] == target &&
                forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches in vector indexing */
    let n = nums.len();
    
    proof {
        lemma_forall_negation_exists(nums, target);
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < n && k1 < k2 ==> nums[k1 as int] + nums[k2 as int] != target,
    {
        let mut j = i + 1;
        while j < n
            invariant
                i < j <= n,
                forall|k2: int| i < k2 < j ==> nums[i as int] + nums[k2 as int] != target,
        {
            proof {
                lemma_vec_len_index_bound_usize(nums, i);
                lemma_vec_len_index_bound_usize(nums, j);
            }
            
            if nums[i] + nums[j] == target {
                proof {
                    lemma_ordered_pair_exists_search(nums, target, i, j, n);
                }
                return Some((i, j));
            }
            j += 1;
        }
        i += 1;
    }
    
    None
}
// </vc-code>

}
fn main() {}