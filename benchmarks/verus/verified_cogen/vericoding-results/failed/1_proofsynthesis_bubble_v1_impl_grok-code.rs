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
/* helper modified by LLM (iteration 4): Added spec function to check multiset preservation for permutation property */
spec fn preserves_multiset(old_nums: Seq<u32>, new_nums: Seq<u32>) -> bool {
    old_nums.to_multiset() =~= new_nums.to_multiset()
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch by casting usize to int for seq indexing in invariants and corrected invariant ranges */
    let mut i = 1;
    proof {
        assert(preserves_multiset(old(nums)@, nums@));
    }
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            sorted_between(nums@, 0, i as int),
            preserves_multiset(old(nums)@, nums@)
        decreases nums.len() - i
    {
        let key = nums[i];
        let mut j = i;
        proof {
            assert(preserves_multiset(old(nums)@, nums@));
        }
        while j > 0 && nums[j - 1] > key
            invariant
                0 <= j <= i,
                sorted_between(nums@, 0, j as int),
                nums@[(j as int)] == key,
                preserves_multiset(old(nums)@, nums@)
            decreases j
        {
            nums[j] = nums[j - 1];
            j = j - 1;
        }
        nums[j] = key;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}