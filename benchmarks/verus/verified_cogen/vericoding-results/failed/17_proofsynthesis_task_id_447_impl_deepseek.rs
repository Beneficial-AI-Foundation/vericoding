// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed trigger annotations and ensured proper lemma structure */
proof fn cube_product_lemma(x: int, y: int, z: int)
    ensures
        x * y * z == x * (y * z),
{
    assert(x * y * z == x * y * z);
    assert(x * (y * z) == x * y * z);
}

proof fn cube_product_lemma2(x: int)
    ensures
        x * x * x == x * (x * x),
{
    cube_product_lemma(x, x, x);
}

proof fn cube_loop_invariant_lemma(nums: &Vec<i32>, cubed: &Vec<i32>, i: int)
    requires
        i >= 0,
        cubed@.len() == i,
        forall|j: int| 0 <= j < i ==> cubed@[j] == nums@[j] * nums@[j] * nums@[j],
    ensures
        i <= nums.len(),
{
}

proof fn push_lemma(cubed: &mut Vec<i32>, num: i32, i: int)
    requires
        old(cubed)@.len() == i,
    ensures
        cubed@.len() == i + 1,
        forall|j: int| 0 <= j < i ==> cubed@[j] == old(cubed)@[j],
        cubed@[i] == num,
{
    assert(cubed@.len() == i + 1);
    assert(forall|j: int| 0 <= j < i ==> cubed@[j] == old(cubed)@[j]);
    assert(cubed@[i] == num);
}
// </vc-helpers>

// <vc-spec>
fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)

    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),

    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed quantifier trigger annotations and type conversions */
{
    let mut cubed = Vec::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            cubed@.len() == i,
            forall|j: int| 0 <= j < i ==> cubed@[j] == nums@[j] * nums@[j] * nums@[j],
        decreases nums.len() - i
    {
        let num = nums[i];
        proof {
            assert(num * num <= i32::MAX as int) by {
                assert(0 <= i < nums.len());
                assert(forall|k: int| 0 <= k < nums.len() ==> i32::MIN <= nums[k] * #[trigger] nums[k] <= i32::MAX);
            };
            assert(num * num * num <= i32::MAX as int) by {
                assert(0 <= i < nums.len());
                assert(forall|k: int| 0 <= k < nums.len() ==> i32::MIN <= nums[k] * #[trigger] nums[k] * #[trigger] nums[k] <= i32::MAX);
            };
            cube_product_lemma2(num as int);
        }
        let product = num * num * num;
        cubed.push(product);
        i += 1;
    }
    cubed
}
// </vc-code>

}
fn main() {}