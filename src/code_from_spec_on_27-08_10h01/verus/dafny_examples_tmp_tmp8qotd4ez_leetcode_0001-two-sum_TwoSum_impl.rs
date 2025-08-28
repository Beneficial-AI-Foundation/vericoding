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
proof fn lemma_map_contains_key_stable(m: Map<int, int>, key: int, new_key: int, new_val: int)
    ensures m.contains_key(key) ==> m.insert(new_key, new_val).contains_key(key)
{
}

proof fn lemma_in_map_extends(nums: Seq<int>, m: Map<int, int>, target: int, i: int)
    requires 0 <= i < nums.len()
    requires in_map(nums.subrange(0, i), m, target)
    ensures in_map(nums.subrange(0, i), m.insert(nums[i], i), target)
{
    let new_m = m.insert(nums[i], i);
    assert forall|j: int| 0 <= j < i implies new_m.contains_key(target - nums[j]) by {
        if 0 <= j < i {
            assert m.contains_key(target - nums[j]);
            lemma_map_contains_key_stable(m, target - nums[j], nums[i], i);
        }
    }
}

proof fn lemma_no_solution_in_prefix(nums: Seq<int>, target: int, k: int)
    requires 0 <= k < nums.len()
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] + nums[j] != target
    ensures forall|i: int, j: int| 0 <= i < j < k ==> nums[i] + nums[j] != target
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
{
    let mut map: Map<int, int> = Map::empty();
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            forall|k: int| 0 <= k < i ==> map.contains_key(nums.view()[k]) && map[nums.view()[k]] == k,
            forall|j: int, k: int| 0 <= j < k < i ==> nums.view()[j] + nums.view()[k] != target,
            in_map(nums.view().subrange(0, i as int), map, target)
    {
        let complement = target - nums[i];
        
        if map.contains_key(complement) {
            let j = map[complement];
            proof {
                assert nums.view()[j] + nums.view()[i as int] == target;
                assert 0 <= j < i;
                lemma_no_solution_in_prefix(nums.view(), target, i as int);
            }
            return (j as i32, i as i32);
        }
        
        proof {
            lemma_in_map_extends(nums.view(), map, target, i as int);
        }
        
        map = map.insert(nums[i], i as int);
        i = i + 1;
    }
    
    proof {
        assert forall|j: int, k: int| 0 <= j < k < nums.len() ==> nums.view()[j] + nums.view()[k] != target by {
            assert i == nums.len();
            assert forall|j: int, k: int| 0 <= j < k < i ==> nums.view()[j] + nums.view()[k] != target;
        }
    }
    
    (-1, -1)
}
// </vc-code>

fn main() {}

}