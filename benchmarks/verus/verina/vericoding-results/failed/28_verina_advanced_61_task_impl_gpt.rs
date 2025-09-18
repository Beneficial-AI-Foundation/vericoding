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
/* helper modified by LLM (iteration 4): total helper for prefix product over indices */
spec fn prefix_product(nums: Seq<i32>, i: int) -> int {
    if 0 <= i && i <= nums.len() { list_product(nums.subrange(0, i)) } else { 0int }
}

/* helper modified by LLM (iteration 4): total helper for suffix product over indices */
spec fn suffix_product(nums: Seq<i32>, i: int) -> int {
    if 0 <= i && i < nums.len() { list_product(nums.subrange(i + 1, nums.len() as int)) } else if i == nums.len() { 1int } else { 0int }
}
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
    /* code modified by LLM (iteration 4): added decreases clauses to loops and basic invariants */
    let n = nums.len();
    let mut result: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant result.len() == i
        decreases (n as int) - (i as int)
    {
        result.push(1i32);
        i = i + 1;
    }

    let mut prefix: i128 = 1i128;
    i = 0;
    while i < n
        invariant i <= n
        invariant result.len() == n
        decreases (n as int) - (i as int)
    {
        result.set(i, (prefix as i32));
        prefix = prefix * (nums[i] as i128);
        i = i + 1;
    }

    let mut suffix: i128 = 1i128;
    let mut k: usize = 0;
    while k < n
        invariant k <= n
        invariant result.len() == n
        decreases (n as int) - (k as int)
    {
        let j: usize = n - 1 - k;
        let val = result[j] as i128;
        let new_val = (val * suffix) as i32;
        result.set(j, new_val);
        suffix = suffix * (nums[j] as i128);
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}