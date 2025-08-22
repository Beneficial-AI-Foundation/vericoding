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
        let ghost original = nums@;
        
        for i in 1..nums.len()
            invariant
                sorted_between(nums@, 0, i as int),
                nums@.len() == original.len(),
                exists|r: Seq<int>| is_reorder_of(r, nums@, original),
        {
            let mut j = i;
            while j > 0 && nums[j - 1] > nums[j]
                invariant
                    0 <= j <= i,
                    nums@.len() == original.len(),
                    j < i ==> sorted_between(nums@, 0, j as int),
                    j < i ==> sorted_between(nums@, (j + 1) as int, (i + 1) as int),
                    j < i ==> (forall|k: int| j < k < i ==> nums@[j as int] <= nums@[k]),
                    exists|r: Seq<int>| is_reorder_of(r, nums@, original),
                /* code modified by LLM (iteration 1): added decreases clause for loop termination */
                decreases j
            {
                /* code modified by LLM (iteration 1): store both values before mutation to avoid borrowing conflicts */
                let temp = nums[j];
                let temp_prev = nums[j - 1];
                nums.set(j, temp_prev);
                nums.set(j - 1, temp);
                j = j - 1;
            }
        }
    }
}