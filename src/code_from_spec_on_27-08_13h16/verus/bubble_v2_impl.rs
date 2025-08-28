use vstd::prelude::*;

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
    forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
}
// pure-end
// pure-end

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// pure-end

// <vc-helpers>
proof fn lemma_swap_preserves_reorder<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>, i: int, j: int)
    requires
        is_reorder_of(r, p, s),
        0 <= i < r.len(),
        0 <= j < r.len(),
    ensures
        is_reorder_of(r.update(i, r[j]).update(j, r[i]), p.update(i, p[j]).update(j, p[i]), s),
{
    let r_swapped = r.update(i, r[j]).update(j, r[i]);
    let p_swapped = p.update(i, p[j]).update(j, p[i]);
    assert(r_swapped.len() == s.len());
    assert(forall|k: int| 0 <= k < r.len() ==> 0 <= r_swapped[k] < r.len());
    assert(forall|k: int, l: int| 0 <= k < l < r.len() ==> r_swapped[k] != r_swapped[l]);
    assert(p_swapped =~= r_swapped.map_values(|k: int| s[k]));
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)
    // post-conditions-start
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let n = nums.len();
    let mut i: usize = 0;
    let mut reorder = Vec::new();
    let ghost initial_nums = nums@;
    while i < n
        invariant
            0 <= i <= n,
            reorder.len() == n,
            forall|k: usize| 0 <= k < n ==> 0 <= reorder[k] < n,
            forall|k: usize, l: usize| 0 <= k < l < n ==> reorder[k] != reorder[l],
            nums@ =~= reorder@.map_values(|k: int| initial_nums[k]),
            sorted_between(nums@, 0, i as int),
    {
        if i == 0 {
            let mut k: usize = 0;
            while k < n {
                reorder.push(k);
                k = k + 1;
            }
        }
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n
            invariant
                i < j <= n,
                i <= min_idx < n,
                reorder.len() == n,
                forall|k: usize| 0 <= k < n ==> 0 <= reorder[k] < n,
                forall|k: usize, l: usize| 0 <= k < l < n ==> reorder[k] != reorder[l],
                nums@ =~= reorder@.map_values(|k: int| initial_nums[k]),
                sorted_between(nums@, 0, i as int),
                forall|k: usize| i <= k < j ==> nums@[(min_idx as int)] <= nums@[(k as int)],
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        if min_idx != i {
            let ghost old_reorder = reorder@;
            let ghost old_nums = nums@;
            let temp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = temp;
            let temp_reorder = reorder[i];
            reorder[i] = reorder[min_idx];
            reorder[min_idx] = temp_reorder;
            proof {
                lemma_swap_preserves_reorder(old_reorder, old_nums, initial_nums, i as int, min_idx as int);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}