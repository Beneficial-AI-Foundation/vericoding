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
        let mut i = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                nums.len() == n,
                sorted_between(nums@, 0, i as int),
                forall|k: int| 0 <= k < i ==> forall|j: int| i <= j < n ==> nums@[k] <= nums@[j],
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut min_idx = i;
            let mut j = i + 1;
            
            while j < n
                invariant
                    i <= min_idx < n,
                    i < j <= n,
                    nums.len() == n,
                    /* code modified by LLM (iteration 1): Fixed type mismatch by casting min_idx and k to int */
                    forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            if min_idx != i {
                let temp = nums[i];
                nums.set(i, nums[min_idx]);
                nums.set(min_idx, temp);
            }
            
            i += 1;
        }
    }
}