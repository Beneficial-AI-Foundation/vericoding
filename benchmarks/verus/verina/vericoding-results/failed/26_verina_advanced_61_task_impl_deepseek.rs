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
/* helper modified by LLM (iteration 2): Fixed exec proof syntax and lemma implementations */
proof fn list_product_empty() -> (p: int)
    ensures p == list_product(Seq::empty())
{
    1int
}

proof fn list_product_recursive(nums: Seq<i32>) -> (p: int)
    requires nums.len() > 0
    ensures p == list_product(nums)
{
    let n = nums.len() as int;
    list_product(nums.subrange(1, n)) * nums[0] as int
}

proof fn list_product_lemma(nums: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= nums.len()
    ensures list_product(nums.subrange(i, j)) == list_product(nums.subrange(j - 1, j)) * list_product(nums.subrange(i, j - 1))
{
    // This lemma will help with the recursive decomposition
    let sub = nums.subrange(i, j);
    if j - i > 1 {
        let first = nums[i] as int;
        let rest = sub.subrange(1, sub.len() as int);
        assert(list_product(sub) == first * list_product(rest));
        list_product_lemma(nums, i + 1, j);
    }
}

spec fn left_product(nums: Seq<i32>, idx: int) -> int
    requires 0 <= idx <= nums.len()
{
    list_product(nums.subrange(0, idx))
}

spec fn right_product(nums: Seq<i32>, idx: int) -> int
    requires 0 <= idx <= nums.len()
{
    list_product(nums.subrange(idx + 1, nums.len() as int))
}

proof fn left_product_lemma(nums: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= nums.len()
    ensures left_product(nums, j) == left_product(nums, i) * list_product(nums.subrange(i, j))
{
    // Recursively decompose the left product
    if i < j {
        left_product_lemma(nums, i, j - 1);
        assert(left_product(nums, j) == left_product(nums, j - 1) * nums[j - 1] as int);
    }
}

proof fn right_product_lemma(nums: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= nums.len()
    ensures right_product(nums, i) == list_product(nums.subrange(i + 1, j)) * right_product(nums, j)
{
    // Recursively decompose the right product
    if i < j {
        right_product_lemma(nums, i + 1, j);
        assert(right_product(nums, i) == nums[i + 1] as int * right_product(nums, i + 1));
    }
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
/* code modified by LLM (iteration 2): Fixed compilation errors and improved loop invariants */
{
    let mut result = Vec::new();
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let n = nums.len();
    result.resize(n, 0);
    left.resize(n, 1);
    right.resize(n, 1);
    
    // Compute prefix products (left to right)
    if n > 0 {
        left[0] = 1;
        for i in 1..n
            invariant
                0 < i <= n,
                forall|j: int| 0 <= j < i ==> left[j] as int == list_product(nums@.subrange(0, j))
        {
            left[i] = left[i - 1] * nums[i - 1];
        }
    }
    
    // Compute suffix products (right to left)
    if n > 0 {
        right[n - 1] = 1;
        for i in (0..n - 1).rev()
            invariant
                0 <= i < n - 1,
                forall|j: int| i < j < n ==> right[j] as int == list_product(nums@.subrange(j + 1, n as int))
        {
            right[i] = right[i + 1] * nums[i + 1];
        }
    }
    
    // Combine left and right products
    for i in 0..n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> result[j] as int == list_product(nums@.subrange(0, j)) * list_product(nums@.subrange(j + 1, n as int))
    {
        result[i] = left[i] * right[i];
    }
    
    result
}
// </vc-code>

}
fn main() {}