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
/* helper modified by LLM (iteration 5): Fixed swap_lemma parameter type to use proof mode */
proof fn reorder_preserves_length<T>(a: Seq<T>, b: Seq<T>, r: Seq<int>)
    requires
        is_reorder_of(r, a, b)
    ensures
        a.len() == b.len()
{
}

proof fn reorder_preserves_permutation<T>(a: Seq<T>, b: Seq<T>, r: Seq<int>)
    requires
        is_reorder_of(r, a, b)
{
}

proof fn sorted_range_lemma(a: Seq<u32>, from: int, to: int, i: int, j: int)
    requires
        sorted_between(a, from, to),
        from <= i < j < to
    ensures
        a[i] <= a[j]
{
}

proof fn swap_lemma(v: &Vec<u32>, i: usize, j: usize)
    requires
        i < old(v)@.len(),
        j < old(v)@.len()
    ensures
        v@ =~= old(v)@.update(i as int, old(v)@[j as int]).update(j as int, old(v)@[i as int]),
        exists|r: Seq<int>| is_reorder_of(r, v@, old(v)@)
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
/* code modified by LLM (iteration 5): Updated swap_lemma call to pass nums as proof reference */
{
    let n = nums.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
    {
        let mut j = i;
        let mut min_index = i;
        
        while j < n
            invariant
                i <= j <= n,
                min_index < n,
                forall|k: int| i <= k < j ==> nums@[min_index as int] <= nums@[k]
        {
            if nums[j] < nums[min_index] {
                min_index = j;
            }
            j += 1;
        }
        
        if min_index != i {
            let temp = nums[i];
            nums[i] = nums[min_index];
            nums[min_index] = temp;
            proof { swap_lemma(&nums, i, min_index); }
        }
        
        i += 1;
    }
}
// </vc-code>

}
fn main() {}