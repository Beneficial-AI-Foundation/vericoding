// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): returns the size of the set of elements in the vector */
fn vec_set_len(v: &Vec<i32>) -> nat {
    v@.to_set().len()
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
    /* code modified by LLM (iteration 3): build unique list without using Seq::slice; use explicit prefix invariants */
    let mut uniq: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            uniq@.no_duplicates(),
            forall|y: i32| uniq@.contains(y) ==> exists|idx: usize| idx < i && nums@[idx] == y,
            forall|idx: usize| idx < i ==> uniq@.contains(nums@[idx]),
        decreases nums.len() - i
    {
        let x: i32 = nums[i];
        if !uniq@.contains(x) {
            uniq.push(x);
        }
        i += 1;
    }
    proof {
        assert(i == nums.len());
        // Every element of uniq was seen in some prefix index < i, and with i == nums.len() that index is in nums
        assert(forall|y: i32| uniq@.contains(y) ==> exists|idx: usize| idx < i && nums@[idx] == y);
        assert(forall|y: i32| uniq@.contains(y) ==> nums@.contains(y));
        // Every element of nums (by index) is contained in uniq after the loop
        assert(forall|idx: usize| idx < i ==> uniq@.contains(nums@[idx]));
        assert(forall|x: i32| nums@.contains(x) ==> exists|idx: usize| idx < i && nums@[idx] == x);
        assert(forall|x: i32| nums@.contains(x) ==> uniq@.contains(x));
        // Hence sets are equal
        assert(uniq@.to_set() == nums@.to_set());
        assert(uniq@.no_duplicates());
        assert(uniq.len() == uniq@.to_set().len());
        assert(uniq.len() == nums@.to_set().len());
    }
    let mut result: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < k
        invariant
            result.len() == j,
            result@.no_duplicates(),
        decreases k - j
    {
        let v: i32 = uniq[j];
        result.push(v);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}