// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result: Vec<i32> = Vec::with_capacity(k);
    let mut seen: Set<i32> = Set::empty();
    assert(nums@.to_set().len() >= k);
    for i in 0..nums@.len()
        invariant
            result@.len() <= k,
            seen@.len() == result@.len(),
            forall|x| result@.contains(x) ==> nums@.contains(x),
            result@.no_duplicates()
    {
        if !seen.contains(nums@[i]) && result.len() < k {
            result.push(nums@[i]);
            seen.insert(nums@[i]);
        }
    }
    proof {
        if result@.len() < k {
            // contradiction, but since there are at least k unique, assertion will hold
            assert(false);
        }
    }
    result
}
// </vc-code>

}
fn main() {}