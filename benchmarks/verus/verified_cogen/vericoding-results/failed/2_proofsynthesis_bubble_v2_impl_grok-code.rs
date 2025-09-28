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
/* helper modified by LLM (iteration 5): No changes needed, as helpers are empty. */
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>

    /* code modified by LLM (iteration 5): Changed loop variables to usize to match Vec indexing and fix compilation errors; updated increments to i = i + 1; adjusted invariants accordingly. */
    let len = nums.len();
    let mut i: usize = 0;
    while (i as int) < (len as int)
        invariant
            0 <= (i as int) <= (len as int),
            nums@.len() == old(nums)@.len(),
            forall |k: int| 0 <= k < (i as int) ==> forall |m: int| (i as int) <= m < (len as int) ==> nums@[k] <= nums@[m],
            exists |r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
        decreases (len as int) - (i as int)
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while (j as int) < (len as int)
            invariant
                (i as int) <= (j as int) <= (len as int),
                (i as int) <= (min_idx as int) < (len as int),
                forall |k: int| (i as int) < k < (j as int) ==> nums@[min_idx as int] <= nums@[k],
                nums@[min_idx as int] <= nums@[i as int],
                nums@.len() == old(nums)@.len(),
                exists |r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
            decreases (len as int) - (j as int)
        {
            if nums[min_idx] > nums[j] {
                min_idx = j;
            }
            j = j + 1;
        }
        let temp = nums[min_idx];
        nums[min_idx] = nums[i];
        nums[i] = temp;
        i = i + 1;
    }

// </vc-code>

}
fn main() {}