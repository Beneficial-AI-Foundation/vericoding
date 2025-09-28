// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed indexing from v@[i] to v[i] for Seq<i32>. */
spec fn no_solution_in_prefix(v: Seq<i32>, target: i32, k: nat) -> bool {
    forall|i: int, j: int| 0 <= i < j < (k as int) ==> v[i] + v[j] != (target as int)
}

/* helper modified by LLM (iteration 5): Changed indexing from v@[i] to v[i] for Seq<i32>. */
proof fn no_solution_prefix_extends(v: Seq<i32>, target: i32, j: nat)
    requires
        j < v.len(),
        no_solution_in_prefix(v, target, j),
        forall|k: int| 0 <= k < (j as int) ==> v[k] + v[j as int] != (target as int),
    ensures
        no_solution_in_prefix(v, target, (j + 1) as nat),
{
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &[i32], target: i32) -> (r: (i32, i32))
    ensures 
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                     nums.view()[r.0 as int] + nums.view()[r.1 as int] == target &&
                     forall|i: int, j: int| 0 <= i < j < r.1 ==> nums.view()[i] + nums.view()[j] != target,
        r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums.view()[i] + nums.view()[j] != target,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed indexing from nums.view()@[k] to nums.view()[k] for Seq<i32>. */
{
    let mut j: usize = 1;
    while j < nums.len()
        invariant
            1 <= j <= nums.len(),
            no_solution_in_prefix(nums.view(), target, j as nat),
        decreases nums.len() - j
    {
        let mut i: usize = 0;
        while i < j
            invariant
                1 <= j < nums.len(),
                0 <= i <= j,
                no_solution_in_prefix(nums.view(), target, j as nat),
                forall|k: int| 0 <= k < (i as int) ==> nums.view()[k] + nums.view()[j as int] != (target as int),
            decreases j - i
        {
            if nums[i] + nums[j] == target {
                return (i as i32, j as i32);
            }
            i = i + 1;
        }
        proof {
            no_solution_prefix_extends(nums.view(), target, j as nat);
        }
        j = j + 1;
    }
    return (-1, -1);
}
// </vc-code>

}
fn main() {}