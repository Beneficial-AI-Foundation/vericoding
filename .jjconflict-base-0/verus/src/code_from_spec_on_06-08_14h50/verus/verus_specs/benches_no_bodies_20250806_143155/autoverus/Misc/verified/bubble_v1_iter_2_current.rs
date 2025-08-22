use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
 
 
    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
    }
 
    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let n = nums.len();
        for i in 0..n
            invariant
                forall|k: int, l: int| 0 <= k < i && i <= l < n ==> nums@[k] <= nums@[l],
                sorted_between(nums@, 0, i as int),
                nums@.len() == old(nums)@.len(),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            for j in (i+1)..n
                invariant
                    i < n,
                    forall|k: int| i <= k < j ==> nums@[i as int] <= nums@[k],
                    forall|k: int, l: int| 0 <= k < i && i <= l < n ==> nums@[k] <= nums@[l],
                    sorted_between(nums@, 0, i as int),
                    nums@.len() == old(nums)@.len(),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j] < nums[i] {
                    /* code modified by LLM (iteration 1): Fixed borrow checker issue by storing values before mutable operations */
                    let temp = nums[i];
                    let val_j = nums[j];
                    nums.set(i, val_j);
                    nums.set(j, temp);
                }
            }
        }
    }
}