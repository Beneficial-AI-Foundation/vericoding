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
/* helper modified by LLM (iteration 4): prove prefix product equals previous prefix times last element */
proof fn list_product_prefix(nums: Seq<i32>, k: int) requires 0 <= k && k <= nums.len() ensures list_product(nums.subrange(0, k)) == if k == 0 { 1 } else { list_product(nums.subrange(0, k - 1)) * nums@(k - 1) as int } decreases k {
    if k == 0 {
    } else {
        if k == 1 {
            assert(list_product(nums.subrange(0,1)) == nums@(0) as int * list_product(nums.subrange(1,1)));
            assert(list_product(nums.subrange(1,1)) == 1);
            assert(list_product(nums.subrange(0,1)) == list_product(nums.subrange(0,0)) * nums@(0) as int);
        } else {
            list_product_prefix(nums.subrange(1, nums.len()), k - 1);
            assert(list_product(nums.subrange(0,k)) == nums@(0) as int * list_product(nums.subrange(1,k)));
            assert(list_product(nums.subrange(1,k)) == list_product(nums.subrange(1,k-1)) * nums@(k-1) as int);
            assert(list_product(nums.subrange(0,k-1)) == nums@(0) as int * list_product(nums.subrange(1,k-1)));
            assert(list_product(nums.subrange(0,k)) == list_product(nums.subrange(0,k-1)) * nums@(k-1) as int);
        }
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
/* code modified by LLM (iteration 4): compute product except self using prefix/suffix arrays with corrected usize/int invariants */
{
    let n = nums.len() as int;

    // build prefix products: prefix[t] = product of nums[0..t-1] (as int), length = n + 1
    let mut prefix: Vec<int> = Vec::new();
    prefix.push(1);
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n,
        invariant prefix.len() == (i + 1) as usize,
        invariant forall|j: int| 0 <= j && j <= i ==> prefix[j as usize] == list_product(nums@.subrange(0, j))
    {
        let last = prefix[prefix.len() - 1];
        let new = last * nums[i as usize] as int;
        prefix.push(new);
        proof {
            // after pushing, prefix length increased and relation for i+1 holds
            list_product_prefix(nums@, i + 1);
        }
        i += 1;
    }

    // build reversed results by walking from end to start using a running suffix product
    let mut res_rev: Vec<i32> = Vec::new();
    let mut suffix: int = 1;
    let mut idx: int = n;
    while idx > 0
        invariant 0 <= idx && idx <= n,
        invariant prefix.len() == (n + 1) as usize,
        invariant suffix == list_product(nums@.subrange(idx, n)),
        invariant res_rev.len() == (n - idx) as usize
    {
        idx -= 1;
        let val = prefix[idx as usize] * suffix;
        res_rev.push(val as i32);
        suffix = suffix * nums[idx as usize] as int;
        proof {
            // maintain suffix invariant via list_product definition on tail
            list_product_prefix(nums@, idx);
        }
    }

    // reverse res_rev into result
    let mut result: Vec<i32> = Vec::new();
    while res_rev.len() > 0
        invariant result.len() + res_rev.len() == n as usize
    {
        let v = res_rev[res_rev.len() - 1];
        res_rev.pop();
        result.push(v);
    }

    // final proof that result satisfies the specification
    proof {
        assert(result.len() as int == n);

        let mut k: int = 0;
        while k < n
            invariant 0 <= k && k <= n,
            invariant forall|j: int| 0 <= j && j < k ==> result[j as usize] as int == list_product(nums@.subrange(0, j)) * list_product(nums@.subrange(j + 1, n))
        {
            list_product_prefix(nums@, k);
            assert(prefix[k as usize] == list_product(nums@.subrange(0, k)));
            assert(result[k as usize] as int == prefix[k as usize] * list_product(nums@.subrange(k + 1, n)));
            assert(result[k as usize] as int == list_product(nums@.subrange(0, k)) * list_product(nums@.subrange(k + 1, n)));
            k += 1;
        }
    }

    result
}

// </vc-code>

}
fn main() {}