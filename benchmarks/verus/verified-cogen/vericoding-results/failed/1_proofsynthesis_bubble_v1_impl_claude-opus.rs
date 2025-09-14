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
    /* code modified by LLM (iteration 5): Fixed borrowing issue in selection sort */
    let n = nums.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            sorted_between(nums@, 0, i as int),
            forall|k: int, l: int| 0 <= k < i <= l < n ==> nums@[k] <= nums@[l],
            nums@.len() == old(nums)@.len(),
            forall|x: u32| old(nums)@.to_multiset().count(x) == nums@.to_multiset().count(x),
        decreases n - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                i < n,
                i <= min_idx < n,
                i < j <= n,
                forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
                nums@.len() == old(nums)@.len(),
                forall|x: u32| old(nums)@.to_multiset().count(x) == nums@.to_multiset().count(x),
            decreases n - j
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = nums[i];
            let val_at_min = nums[min_idx];
            nums.set(i, val_at_min);
            nums.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    proof {
        let identity = Seq::new(n as nat, |k: int| k);
        assert(is_reorder_of(identity, nums@, old(nums)@));
    }
}
// </vc-code>

}
fn main() {}