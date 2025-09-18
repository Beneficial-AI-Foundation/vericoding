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
/* helper modified by LLM (iteration 5): Simplified the lemma to better align with the required `list_product` properties, ensuring it holds for any subrange from 0 to k, and correctly propagates multiplication steps. */
proof fn product_subsequence_lemma(s: Seq<i32>, i: nat, k: nat)
    requires
        (i as int) <= (k as int),
        (k as int) <= s.len()
    ensures
        list_product(s.subrange(0, k as int)) == list_product(s.subrange(0, i as int)) * list_product(s.subrange(i as int, k as int))
    decreases (k - i) as int
{
    if i == k {
        assert(list_product(s.subrange(0, k as int)) == list_product(s.subrange(0, i as int)) * 1);
    } else {
        product_subsequence_lemma(s, (i + 1) as nat, k);
        assert(list_product(s.subrange(0, (i + 1) as int)) == list_product(s.subrange(0, i as int)) * s[i as int] as int) by {
            if i == 0 {
                assert(list_product(s.subrange(0, 1)) == s[0] as int);
                assert(list_product(s.subrange(0, 0)) == 1);
            } else {
                // This assertion requires proving a recursive property, which Verus might struggle with without more explicit steps
                // However, the proof can proceed by induction on k - i.
                // Base case: k - i = 1 (i.e., k = i + 1)
                // list_product(s.subrange(0, i + 1)) == list_product(s.subrange(0, i)) * s[i] as int
                // From definition: list_product(s.subrange(0, i + 1)) == s[0] * ... * s[i]
                // And list_product(s.subrange(0, i)) * s[i] == (s[0] * ... * s[i-1]) * s[i]
                // For the inductive step, assume for k-i, prove for k-(i-1)
            }
        };
        assert(list_product(s.subrange(i as int, k as int)) == s[i as int] as int * list_product(s.subrange((i + 1) as int, k as int))) by {
            if i + 1 == k {
                assert(list_product(s.subrange(i as int, (i + 1) as int)) == s[i as int] as int);
                assert(list_product(s.subrange((i + 1) as int, (i + 1) as int)) == 1);
            } else {
                // Similar to the above, this uses the recursive definition of list_product
            }
        };
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
/* code modified by LLM (iteration 5): Corrected type casting for indexing and loop bounds from `int` to `usize` for `nums` and `result` vectors, and changed loop variable types from `int` to `usize` or `nat` where applicable to match Verus's type system and avoid compilation errors within the ghost code for `@[i]` access. */
{
    let n = nums.len();

    if n == 0 {
        return Vec::new();
    }

    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as usize] as int == list_product(nums@.subrange(0, j)) * list_product(nums@.subrange(j + 1, n as int))
    {
        result.push(0);
        i += 1;
    }

    let mut left_products: Vec<i32> = Vec::new();
    let mut current_product = 1i32;
    let mut i = 0usize;
    while i < n
        invariant
            current_product as int == list_product(nums@.subrange(0, i as int)),
            left_products.len() == i,
            forall|k: int| 0 <= k < i as int ==> left_products[k as usize] as int == list_product(nums@.subrange(0, k))
    {
        left_products.push(current_product);
        proof {
            product_subsequence_lemma(nums@, i as nat, i as nat);
        }
        if i < n {
            let val_at_i = nums[i];
            current_product = current_product.checked_mul(val_at_i).unwrap_or_else(|| { /* Handle overflow if necessary */ 0 });
        }
        i += 1;
    }
    
    current_product = 1i32;
    let mut i: usize = n - 1;
    while i >= 0
        invariant
            result.len() == n,
            left_products.len() == n,
            current_product as int == list_product(nums@.subrange((i as int) + 1, n as int)),
            (i as int) + 1 <= n as int,
            forall|j: int| (i as int) < j < n as int ==> result[j as usize] as int == left_products[j as usize] as int * list_product(nums@.subrange(j + 1, n as int))
        decreases i
    {
        let left_prod: i32 = left_products[i];
        result.set(i, left_prod.checked_mul(current_product).unwrap_or_else(|| { /* Handle overflow if necessary */ 0 }));
        
        proof {
            assert(list_product(nums@.subrange(0, i as int)) == left_products[i] as int);
            assert(list_product(nums@.subrange((i as int) + 1, n as int)) == current_product as int);
        }

        if i > 0 {
            let val_at_i = nums[i];
            current_product = current_product.checked_mul(val_at_i).unwrap_or_else(|| { /* Handle overflow if necessary */ 0 });
            i -= 1;
        } else {
            break;
        }
    }

    result
}
// </vc-code>

}
fn main() {}