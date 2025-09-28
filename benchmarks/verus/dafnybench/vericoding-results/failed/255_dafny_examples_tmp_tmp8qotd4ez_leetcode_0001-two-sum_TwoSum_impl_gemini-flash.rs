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
use std::ops::Index;

#[verifier(external_body)]
#[inline(always)]
fn get_vec_idx<T>(v: &Vec<T>, i: int) -> T {
    v.index(i as usize).clone()
}

proof fn lemma_div_by_2_pos(a: int)
    requires a > 0
    ensures a / 2 < a
{}

proof fn lemma_le_transitive(a: int, b: int, c: int)
    requires a <= b, b <= c
    ensures a <= c
{}

proof fn lemma_lt_transitive(a: int, b: int, c: int)
    requires a < b, b < c
    ensures a < c
{}

proof fn lemma_lt_not_le(a: int, b: int)
    requires a < b
    ensures !(b <= a)
{}

proof fn lemma_le_not_lt(a: int, b: int)
    requires a <= b
    ensures !(b < a)
{}
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
    let mut map = Map::<i32, i32>::empty();
    let mut i: int = 0;

    // First pass to build the map
    #[verifier::loop_invariant(
        0 <= i && i <= (nums.len() as int),
        forall|k: int| 0 <= k < i ==> map.contains_key(nums.view()[k]) && map[nums.view()[k]] == k
    )]
    while i < (nums.len() as int)
    {
        map = map.insert(nums.view()[i], i as i32);
        i = i + 1;
    }

    // Second pass to find the pair
    let mut j: int = 0;
    #[verifier::loop_invariant(
        0 <= j && j <= (nums.len() as int),
        forall|idx: int| 0 <= idx < j ==> !(map.contains_key(target - nums.view()[idx]) && map[target-nums.view()[idx]] != idx as i32
         && (map[target-nums.view()[idx]] < idx as i32 ==> nums.view()[map[target-nums.view()[idx]] as int] + nums.view()[idx as int] == target )
         && (idx as i32 < map[target-nums.view()[idx]] ==> nums.view()[idx as int] + nums.view()[map[target-nums.view()[idx]] as int] == target )
        ),
        forall|k: int| 0 <= k < (nums.len() as int) ==> map.contains_key(nums.view()[k]) && map[nums.view()[k]] == k as i32
    )]
    while j < (nums.len() as int)
    {
        let complement = target - nums.view()[j];
        if map.contains_key(complement) {
            let k = map.get(complement).unwrap();
            proof {
                assert(map.contains_key(complement));
                assert(map[complement] == k);
            }
            if k != j as i32 {
                if k < j as i32 {
                    return (k, j as i32);
                } else {
                    return (j as i32, k);
                }
            }
        }
        j = j + 1;
    }

    (-1, -1)
}
// </vc-code>

fn main() {}

}