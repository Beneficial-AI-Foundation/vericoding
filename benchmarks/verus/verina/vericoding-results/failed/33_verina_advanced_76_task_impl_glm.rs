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
    /* code modified by LLM (iteration 2): fix type error in invariant by removing unnecessary cast */
    let mut distinct = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            distinct@.no_duplicates(),
            forall|j: int| 0 <= j < distinct.len() ==> nums@.contains(distinct[j]),
            distinct.len() <= k,
            i as int <= nums@.len(),
        decreases nums@.len() - (i as int)
    {
        let num = nums[i];
        if !distinct.contains(&num) {
            distinct.push(num);
            if distinct.len() == k {
                break;
            }
        }
        i += 1;
    }
    distinct
}
// </vc-code>

}
fn main() {}