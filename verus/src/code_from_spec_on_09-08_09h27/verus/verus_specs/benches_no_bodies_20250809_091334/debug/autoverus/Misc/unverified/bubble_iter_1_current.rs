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
                sorted_between(nums@, 0, i as int),
                forall|j: int, k: int| 0 <= j < i && i <= k < nums.len() ==> nums@[j] <= nums@[k],
                nums@.len() == n,
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut min_idx = i;
            for j in (i + 1)..n
                invariant
                    i <= min_idx < n,
                    forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
                    nums@.len() == n,
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
            }
            
            if min_idx != i {
                let temp = nums[i];
                nums.set(i, nums[min_idx]);
                nums.set(min_idx, temp);
            }
        }
    }
}