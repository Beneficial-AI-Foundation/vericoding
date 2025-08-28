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
use vstd::map::*;

spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}

proof fn map_contains_key_after_insert(m: Map<int, int>, k: int, v: int, k2: int)
    ensures
        m.insert(k, v).contains_key(k2) == (k == k2 || m.contains_key(k2))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn two_sum(nums: &[i32], target: i32) -> (r: (i32, i32))
    ensures 
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                     nums.view()[r.0 as int] + nums.view()[r.1 as int] == target &&
                     forall|i: int, j: int| 0 <= i < j < r.1 ==> nums.view()[i] + nums.view()[j] != target,
        r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums.view()[i] + nums.view()[j] != target,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn two_sum(nums: &[i32], target: i32) -> (r: (i32, i32))
    ensures 
        r.0 >= 0 ==> 0 <= r.0 < r.1 < nums.len() as i32 && 
                     nums.view()[r.0 as int] + nums.view()[r.1 as int] == target as int &&
                     forall|i: int, j: int| 0 <= i < j < r.1 as int ==> nums.view()[i] + nums.view()[j] != target as int,
        r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums.len() as int ==> nums.view()[i] + nums.view()[j] != target as int,
{
    let mut map: Map<int, int> = Map::empty();
    let mut i: usize = 0;

    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k: int, v: int| map.contains_pair(k, v) ==> 0 <= v < i as int,
            forall|j1: int, j2: int| 0 <= j1 < j2 < i as int ==> nums.view()[j1] + nums.view()[j2] != target as int,
    {
        let num = nums[i] as int;
        let complement = target as int - num;
        if map.contains_key(complement) {
            let idx = map[complement];
            return (idx as i32, i as i32);
        }
        map = map.insert(num, i as int);
        proof {
            map_contains_key_after_insert(map.remove(num), num, i as int, complement);
        }
        i = i + 1;
    }

    (-1, -1)
}
// </vc-code>

fn main() {}

}