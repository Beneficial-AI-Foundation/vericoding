// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
    forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
}

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error - replaced && with && in invariant */
    let n = nums.len();
    
    // Create identity permutation to satisfy initial invariant
    proof {
        let identity = Seq::new(n as nat, |i: int| i);
        assert(is_reorder_of(identity, nums@, nums@));
    }
    
    for i in 0..n
        invariant
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            nums@.len() == n,
    {
        let mut min_idx = i;
        for j in (i + 1)..n
            invariant
                i <= min_idx < n,
                nums@.len() == n,
                forall|k: int| i as int <= k < j as int ==> min_idx as int < nums@.len() && k < nums@.len() && nums@[min_idx as int] <= nums@[k],
        {
            if j < nums.len() && min_idx < nums.len() && nums[j] < nums[min_idx] {
                min_idx = j;
            }
        }
        if min_idx != i && i < nums.len() && min_idx < nums.len() {
            let temp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = temp;
        }
    }
}
// </vc-code>

}
fn main() {}