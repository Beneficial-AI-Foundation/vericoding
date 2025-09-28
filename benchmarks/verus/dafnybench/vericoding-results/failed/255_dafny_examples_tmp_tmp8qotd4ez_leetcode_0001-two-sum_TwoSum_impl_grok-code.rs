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
#[verifier::opaque]
spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
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
{
    let mut i: int = 0;
    while i < nums.view().len()
        decreases nums.view().len() - i
    {
        invariant 0 <= i <= nums.view().len()
        invariant forall |a: int, b: int|
            #![trigger nums.view()[a]]
            #![trigger nums.view()[b]]
            0 <= a < b < i ==> nums.view()[a] + nums.view()[b] != target
        let mut j: int = i + 1;
        while j < nums.view().len()
            decreases nums.view().len() - j
        {
            invariant i + 1 <= j <= nums.view().len()
            if nums.view()[i] + nums.view()[j] == target {
                return (i as i32, j as i32);
            }
            j += 1;
        }
        i += 1;
    }
    return (-1, -1);
}
// </vc-code>

fn main() {}

}