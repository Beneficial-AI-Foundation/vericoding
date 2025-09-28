use vstd::prelude::*;

verus! {

// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}

// <vc-helpers>

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
{
    let n = nums.len();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            forall|i:int, jj:int| 0 <= i && i < jj && jj < j as int ==> nums.view()[i] + nums.view()[jj] != target,
    {
        let mut i: usize = 0;
        while i < j
            invariant
                i <= j,
                forall|ii:int, jj:int| 0 <= ii && ii < jj && jj < j as int ==> nums.view()[ii] + nums.view()[jj] != target,
                forall|ii:int| 0 <= ii && ii < i as int ==> nums.view()[ii] + nums.view()[j as
// </vc-code>

fn main() {}

}