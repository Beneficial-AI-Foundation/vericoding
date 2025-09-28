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
spec fn in_map_at(nums: Seq<i32>, m: Map<i32, i32>, t: i32, k: int) -> bool {
    forall|j: int| 0 <= j < k ==> m.contains_key(t - nums[j])
}

proof fn lemma_in_map_extend(nums: Seq<i32>, m: Map<i32, i32>, t: i32, k: int, new_key: i32, new_val: i32)
    requires 
        0 <= k < nums.len(),
        in_map_at(nums, m, t, k)
    ensures 
        in_map_at(nums, m.insert(new_key, new_val), t, k)
{
}

proof fn lemma_in_map_step(nums: Seq<i32>, m: Map<i32, i32>, t: i32, k: int)
    requires 
        0 <= k < nums.len(),
        in_map_at(nums, m, t, k),
        m.contains_key(t - nums[k])
    ensures 
        in_map_at(nums, m, t, k + 1)
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
{
    let mut m: Map<i32, i32> = Map::empty();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k: int| 0 <= k < i ==> m.contains_key(nums.view()[k]),
            forall|k: int| 0 <= k < i ==> m.index(nums.view()[k]) == k,
            forall|j: int, k: int| 0 <= j < k < i ==> nums.view()[j] + nums.view()[k] != target,
    {
        let complement = target - nums[i];
        
        if m.contains_key(complement) {
            let j = m.index(complement);
            
            assert(0 <= j < i);
            assert(nums.view()[j as int] + nums.view()[i as int] == target);
            assert(forall|x: int, y: int| 0 <= x < y < i ==> nums.view()[x] + nums.view()[y] != target);
            
            return (j, i as i32);
        }
        
        proof {
            lemma_in_map_extend(nums.view(), m, target, i as int, nums[i as int], i as i32);
        }
        
        m = m.insert(nums[i], i as i32);
        i += 1;
    }
    
    assert(forall|j: int, k: int| 0 <= j < k < nums.len() ==> nums.view()[j] + nums.view()[k] != target);
    
    (-1, -1)
}
// </vc-code>

fn main() {}

}