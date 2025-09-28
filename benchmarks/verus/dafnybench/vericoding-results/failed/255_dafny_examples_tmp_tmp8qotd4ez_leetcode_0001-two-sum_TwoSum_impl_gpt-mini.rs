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
// Helper lemmas are not required for this implementation.
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
    let n: int = nums.len() as int;
    let mut m = Map::<i32, int>::new();
    let mut j: int = 0;
    while j < n
        invariant 0 <= j && j <= n;
        invariant forall|k: int| 0 <= k && k < j ==> m.contains_key(nums.view()[k]);
        invariant forall|val: i32, idx: int| m.get(val) == Option::Some(idx) ==> 0 <= idx && idx < j;
        invariant forall|val: i32, idx: int| m.get(val) == Option::Some(idx) ==> nums.view()[idx] == val;
        invariant forall|k: int, i: int| 0 <= k && k < j && 0 <= i && i < k ==> nums.view()[i] + nums.view()[k] != target;
        decreases n - j;
    {
        let x: i32 = nums[j as usize];
        let want: i32 = target - x;
        match m.get(want) {
            Option::Some(ii) => {
                assert(0 <= ii);
                assert(ii < j);
                assert(nums.view()[ii] == want);
                assert(nums.view()[ii] + nums.view()[j] == target);
                return (ii as i32, j as i32);
            }
            Option::None => {
                m = m.insert(x, j);
                j += 1;
            }
        }
    }
    (-1, -1)
}
// </vc-code>

fn main() {}

}