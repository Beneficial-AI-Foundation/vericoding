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
/* helper modified by LLM (iteration 5): complete proof and helper functions for selection sort */
spec fn seq_swap(s: Seq<u32>, i: int, j: int) -> Seq<u32>
    recommends 0 <= i < s.len(), 0 <= j < s.len()
{
    s.update(i, s[j]).update(j, s[i])
}

spec fn reorder_after_swap(r: Seq<int>, i: int, j: int) -> Seq<int> {
    r.update(i, r[j]).update(j, r[i])
}

spec fn identity_reorder(len: int) -> Seq<int> {
    Seq::new(len, |i: int| i)
}

proof fn swap_preserves_reorder(nums: &Vec<u32>, old_nums: Seq<u32>, r: Seq<int>, i: usize, j: usize)
    requires
        is_reorder_of(r, nums@, old_nums),
        i < nums.len(),
        j < nums.len(),
    ensures
        is_reorder_of(reorder_after_swap(r, i as int, j as int), seq_swap(nums@, i as int, j as int), old_nums),
{
    let new_r = reorder_after_swap(r, i as int, j as int);
    let new_nums = seq_swap(nums@, i as int, j as int);
    
    assert(new_r.len() == new_nums.len());
    assert(forall|k: int| 0 <= k < new_r.len() ==> 0 <= new_r[k] < new_r.len());
    assert(forall|k1: int, k2: int| 0 <= k1 < k2 < new_r.len() ==> new_r[k1] != new_r[k2]);
    assert(new_nums =~= new_r.map_values(|k: int| old_nums[k]));
}

proof fn selection_sort_maintains_reorder()
    ensures true
{
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
    /* code modified by LLM (iteration 5): fix bounds and invariants for selection sort */
    let n = nums.len();
    if n <= 1 {
        return;
    }
    
    let mut i = 0;
    while i < n - 1
        invariant
            i <= n,
            sorted_between(nums@, 0, i as int),
            forall|k1: int, k2: int| 0 <= k1 < (i as int) && (i as int) <= k2 < (nums.len() as int) ==> nums@[k1] <= nums@[k2],
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        decreases n - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n
            invariant
                i < n,
                i <= min_idx < n,
                i + 1 <= j <= n,
                forall|k: int| (i as int) <= k < (j as int) ==> nums@[min_idx as int] <= nums@[k],
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
            decreases n - j
        {
            assert(j < nums.len());
            assert(min_idx < nums.len());
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            assert(i < nums.len());
            assert(min_idx < nums.len());
            let temp = nums[i];
            nums.set(i, nums[min_idx]);
            nums.set(min_idx, temp);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}