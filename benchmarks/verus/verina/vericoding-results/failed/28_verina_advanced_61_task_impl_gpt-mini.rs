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
/* helper modified by LLM (iteration 5): lemma for list_product cons-case */
proof fn list_product_cons(s: Seq<i32>)
    requires s.len() > 0,
    ensures list_product(s) == s[0] as int * list_product(s.subrange(1, s.len() as int)),
{
    proof {
        assert(list_product(s) == s[0] as int * list_product(s.subrange(1, s.len() as int)));
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
    /* code modified by LLM (iteration 5): compute prefix and suffix products with consistent index types and fixed quantifiers */
    let n: usize = nums.len();
    if n == 0 {
        return Vec::new();
    }

    // Build prefix products: pref[i] = product of nums[0..i)
    let mut pref: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            pref.len() == j,
            forall|t: int| 0 <= t && t < j as int ==> pref[t as usize] as int == list_product(nums@.subrange(0int, t)),
        decreases n - j
    {
        if j == 0 {
            pref.push(1i32);
        } else {
            let prev = pref[j - 1];
            let v = prev * nums[j - 1];
            pref.push(v);
        }
        j += 1;
    }

    // Initialize result vector with dummy values so we can set by index
    let mut result: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
        decreases n - k
    {
        result.push(1i32);
        k += 1;
    }

    // Traverse from right to left maintaining suffix = product of nums[i+1..n)
    let mut suffix: i32 = 1i32;
    let mut idx: usize = n;
    while idx > 0
        invariant
            idx <= n,
            suffix as int == list_product(nums@.subrange(idx as int, n as int)),
        decreases idx
    {
        idx -= 1;
        let val = pref[idx] * suffix;
        result.set(idx, val);
        // update suffix to be product of nums[idx..n)
        suffix = nums[idx] * suffix;
    }

    result
}
// </vc-code>

}
fn main() {}