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
// Helper to establish that if we find a match, no earlier pair exists
proof fn no_earlier_pair(nums: Seq<i32>, m: Map<i32, i32>, i: int, target: i32)
    requires
        0 <= i < nums.len(),
        m.contains_key((target - nums[i]) as i32),
        forall|k: i32| #[trigger] m.contains_key(k) ==> exists|v: i32| m[k] == v && 0 <= v < i && nums[v as int] == k,
        forall|v: i32| 0 <= v < i ==> #[trigger] nums[v as int] == nums[v as int] && m.contains_key(nums[v as int]) && m[nums[v as int]] == v,
    ensures
        forall|j: int, k: int| 0 <= j < k < i + 1 && nums[j] as int + nums[k] as int == target as int ==> 
            j == m[(target - nums[i]) as i32] as int && k == i,
{
    assert forall|j: int, k: int| 0 <= j < k < i + 1 && nums[j] as int + nums[k] as int == target as int implies 
        j == m[(target - nums[i]) as i32] as int && k == i by {
        if 0 <= j < k < i + 1 && nums[j] as int + nums[k] as int == target as int {
            if k < i {
                // Both j and k are before i, so nums[j] should be in map
                assert(nums[k] == (target - nums[j]) as i32);
                assert(m.contains_key(nums[j]));
                assert(m[nums[j]] == j as i32);
                // This contradicts that no solution was found earlier
            } else {
                // k == i
                assert(nums[j] == (target - nums[i]) as i32);
                assert(m.contains_key((target - nums[i]) as i32));
                assert(m[(target - nums[i]) as i32] == j as i32);
            }
        }
    }
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
    use std::collections::HashMap;
    
    let mut m: HashMap<i32, i32> = HashMap::new();
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k: i32| #[trigger] m@.contains_key(k) ==> 
                exists|v: i32| m@[k] == v && 0 <= v < i && nums@[v as int] == k,
            forall|j: int| 0 <= j < i ==> #[trigger] nums@[j] == nums@[j] && m@.contains_key(nums@[j]) && m@[nums@[j]] == j as i32,
            forall|j: int, k: int| 0 <= j < k < i ==> nums@[j] as int + nums@[k] as int != target as int,
        decreases nums.len() - i
    {
        let complement = target - nums[i];
        
        if m.contains_key(&complement) {
            let j = *m.get(&complement).unwrap();
            
            proof {
                no_earlier_pair(nums@, m@, i as int, target);
            }
            
            return (j, i as i32);
        }
        
        m.insert(nums[i], i as i32);
        i = i + 1;
    }
    
    (-1, -1)
}
// </vc-code>

fn main() {}

}