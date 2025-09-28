// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): contains check and spec helper for scanned prefix membership */
fn vec_contains(v: &Vec<i32>, x: i32) -> bool {
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len(),
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

spec fn scanned_contains(nums: Seq<i32>, i: nat, x: i32) -> bool {
    exists|j: nat| j < i && nums.index(j as int) == x
}

// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): collect first k distinct elements preserving invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len() && result.len() < k
        invariant
            result.len() <= k,
            forall|x: i32| result@.contains(x) ==> nums@.contains(x),
            result@.no_duplicates(),
        decreases nums.len() - i
    {
        let cur = nums[i];
        if !vec_contains(&result, cur) {
            result.push(cur);
        }
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}