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
/* helper modified by LLM (iteration 3): re-validated existing helpers */
proof fn lemma_product_cons(v: i32, s: Seq<i32>)
    ensures list_product(s.insert(0, v)) == v as int * list_product(s),
{
}

/* helper modified by LLM (iteration 3): re-validated existing helpers */
proof fn lemma_product_push(s: Seq<i32>, v: i32)
    ensures list_product(s.push(v)) == list_product(s) * (v as int),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_product_push(s.subrange(1, s.len() as int), v);
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
{
    /* code modified by LLM (iteration 3): added decreases clauses to loops */
    let n = nums.len();
    let mut result: Vec<i32> = Vec::with_capacity(n);

    // Pass 1: compute prefix products
    let mut left_product: i32 = 1;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            nums.len() == n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] as int == list_product(nums@.subrange(0, j)),
            left_product as int == list_product(nums@.subrange(0, i as int)),
        decreases n - i,
    {
        result.push(left_product);
        let num_i = nums[i];
        proof {
            lemma_product_push(nums@.subrange(0, i as int), num_i);
        }
        left_product = left_product * num_i;
        i = i + 1;
    }

    // Pass 2: compute suffix products and finalize the result
    let mut right_product: i32 = 1;
    let mut j: usize = n;
    while j > 0
        invariant
            j <= n,
            nums.len() == n,
            result.len() == n,
            forall|k: int| j as int <= k < n as int ==>
                #[trigger] result[k] as int == list_product(nums@.subrange(0, k)) * list_product(nums@.subrange(k + 1, n as int)),
            forall|k: int| 0 <= k < j as int ==>
                #[trigger] result[k] as int == list_product(nums@.subrange(0, k)),
            right_product as int == list_product(nums@.subrange(j as int, n as int)),
        decreases j,
    {
        j = j - 1;
        
        let old_result_j = result[j];
        result.set(j, old_result_j * right_product);

        let num_j = nums[j];
        proof {
            lemma_product_cons(num_j, nums@.subrange(j as int + 1, n as int));
        }
        right_product = right_product * num_j;
    }

    result
}
// </vc-code>

}
fn main() {}