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
/* helper modified by LLM (iteration 5): fix find_index_for_position return value and add proper spec function body */
spec fn find_index_for_position(r: Seq<int>, pos: int) -> int 
    requires 
        0 <= pos < r.len()
    ensures 
        0 <= result < r.len() && r[result] == pos
{
    choose|i: int| 0 <= i < r.len() && r[i] == pos
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix result variable scope and add proper bubble sort implementation */
{
    let n = nums.len();
    let old_nums = old(nums)@;
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            exists|r: Seq<int>| is_reorder_of(r, nums@, old_nums)
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                exists|r: Seq<int>| is_reorder_of(r, nums@, old_nums)
        {
            if nums[j] > nums[j + 1] {
                let temp = nums[j];
                nums[j] = nums[j + 1];
                nums[j + 1] = temp;
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old_nums));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_reorder_sorted_same(nums@, old_nums);
    }
    
    assert(sorted_between(nums@, 0, nums@.len() as int));
}
// </vc-code>

}
fn main() {}