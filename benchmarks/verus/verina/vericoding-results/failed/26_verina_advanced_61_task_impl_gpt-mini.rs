// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn list_product(nums: Seq<i32>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 1int } else { nums[0] as int * list_product(nums.subrange(1, nums.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int for spec indices */
spec fn usize_to_int(u: usize) -> int { u as int }
// </vc-helpers>

// <vc-spec>
fn product_except_self(nums: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 
            result[i] as int == list_product(nums@.subrange(0, i)) * list_product(nums@.subrange(i + 1, nums.len() as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute prefix and suffix products with correct int literals and casts */
    let n = nums.len();

    let mut prefix: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n + 1
        invariant
            i <= n + 1,
            prefix.len() == i,
            forall|k: int| 0int <= k < (i as int) ==> prefix[k as usize] as int == list_product(nums@.subrange(0int, k)),
        decreases n + 1 - i
    {
        if i == 0 {
            prefix.push(1);
        } else {
            let next = prefix[i - 1] * nums[i - 1];
            prefix.push(next);
        }
        i += 1;
    }

    let mut suffix: Vec<i32> = Vec::new();
    let mut t: usize = 0;
    while t < n + 1
        invariant
            t <= n + 1,
            suffix.len() == t,
        decreases n + 1 - t
    {
        suffix.push(0);
        t += 1;
    }
    suffix[n] = 1;

    let mut k: usize = n;
    while k > 0
        invariant
            k <= n,
            suffix.len() == n + 1,
            forall|idx: int| (k as int) <= idx <= (n as int) ==> suffix[idx as usize] as int == list_product(nums@.subrange(idx, nums.len() as int)),
        decreases k
    {
        k -= 1;
        suffix[k] = nums[k] * suffix[k + 1];
    }

    let mut result: Vec<i32> = Vec::new();
    let mut ii: usize = 0;
    while ii < n
        invariant
            ii <= n,
            result.len() == ii,
        decreases n - ii
    {
        let val = prefix[ii] * suffix[ii + 1];
        result.push(val);
        ii += 1;
    }

    proof {
        assert(forall|idx: int| 0int <= idx && idx < (n as int) ==>
            result[idx as usize] as int == list_product(nums@.subrange(0int, idx)) * list_product(nums@.subrange(idx + 1int, nums.len() as int))
        );
    }

    result
}

// </vc-code>

}
fn main() {}