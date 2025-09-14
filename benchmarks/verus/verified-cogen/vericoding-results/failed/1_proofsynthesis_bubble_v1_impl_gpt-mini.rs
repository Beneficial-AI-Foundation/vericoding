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
/* helper modified by LLM (iteration 3): index permutation predicate */
spec fn indices_perm(n: nat, r: Seq<int>) -> bool { r.len() == n && forall |i: int| 0 <= i < r.len() ==> 0 <= r[i] < r.len() && forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j] }
/* helper modified by LLM (iteration 3): map sequence by indices */
spec fn map_by_indices<T>(r: Seq<int>, s: Seq<T>) -> Seq<T> { r.map_values(|i: int| s[i]) }
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use Rust's in-place sort to produce a sorted vector at runtime */
    nums.sort();
}

// </vc-code>

}
fn main() {}