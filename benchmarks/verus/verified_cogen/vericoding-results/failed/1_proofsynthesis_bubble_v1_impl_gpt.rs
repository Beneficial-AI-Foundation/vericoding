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
/* helper modified by LLM (iteration 5): bounds-checked swap with specs preserving length and describing effect */
fn swap_in_vec(nums: &mut Vec<u32>, i: usize, j: usize)
    requires
        i < nums.len(),
        j < nums.len()
    ensures
        nums.len() == old(nums.len()),
        nums@.len() == old(nums)@.len(),
        forall|k: int| 0 <= k < nums@.len() ==>
            if k == i as int { nums@[k] == old(nums)@[j as int] }
            else if k == j as int { nums@[k] == old(nums)@[i as int] }
            else { nums@[k] == old(nums)@[k] }
{
    if i != j {
        let vi = nums[i];
        let vj = nums[j];
        nums[i] = vj;
        nums[j] = vi;
    }
}

/* helper modified by LLM (iteration 5): min helper for u32 */
fn min_u32(a: u32, b: u32) -> u32 { if a < b { a } else { b } }

/* helper modified by LLM (iteration 5): predicate alias for sorted */
spec fn is_sorted_seq_u32(a: Seq<u32>) -> bool { sorted_between(a, 0, a.len() as int) }
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection sort with strengthened invariants and safe swap preconditions */
    let n = nums.len();
    let mut i: usize = 0;
    while i < n
        invariant
            nums.len() == n,
            i <= n
        decreases n - i
    {
        let mut min_j: usize = i;
        // j starts at i+1; safe if i < n; otherwise loop not entered
        let mut j: usize = i + 1;
        assert(i < n);
        while j < n
            invariant
                nums.len() == n,
                i < n,
                i <= min_j,
                min_j < n,
                j >= i + 1,
                j <= n
            decreases n - j
        {
            if nums[j] < nums[min_j] {
                min_j = j;
            }
            j += 1;
        }
        if min_j != i {
            // safe by invariants: i < n and min_j < n
            swap_in_vec(nums, i, min_j);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}