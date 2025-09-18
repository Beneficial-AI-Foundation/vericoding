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

// </vc-helpers>

// <vc-spec>
fn product_except_self(nums: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 
            result[i] as int == list_product(nums@.subrange(0, i)) * list_product(nums@.subrange(i + 1, nums.len() as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariants by adding curly braces */
{
    let n = nums.len();
    let mut result = Vec::new();
    for _ in 0..n {
        result.push(0);
    }

    if n == 0 {
        return result;
    }

    let mut prefix = Vec::new();
    for _ in 0..n {
        prefix.push(1);
    }
    for i in 1..n
        invariant {
            1 <= i <= n
        }
        invariant {
            forall|k: int| 0 <= k < i ==> prefix[k] as int == list_product(nums@.subrange(0, k))
        }
    {
        prefix[i] = prefix[i-1] * nums[i-1];
    }

    let mut suffix = Vec::new();
    for _ in 0..n {
        suffix.push(1);
    }
    let mut i = n - 2;
    while i >= 0
        invariant {
            -1 <= i <= n-1
        }
        invariant {
            forall|k: int| i+1 <= k < n ==> suffix[k] as int == list_product(nums@.subrange(k+1, n as int))
        }
    {
        suffix[i] = suffix[i+1] * nums[i+1];
        i -= 1;
    }

    for i in 0..n
        invariant {
            0 <= i <= n
        }
        invariant {
            forall|k: int| 0 <= k < i ==> 
                result[k] as int == list_product(nums@.subrange(0, k)) * list_product(nums@.subrange(k+1, n as int))
        }
    {
        result[i] = prefix[i] * suffix[i];
    }

    result
}
// </vc-code>

}
fn main() {}