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
proof fn lemma_in_map_empty(m: Map<int, int>, t: int)
    ensures in_map(Seq::<int>::empty(), m, t),
{
    assert forall|j: int| 0 <= j < 0 ==> m.contains_key(t - 0) by {
        unfold(0 <= j < 0);
    }
}

proof fn lemma_in_map_insert(nums: Seq<int>, m: Map<int, int>, t: int, i: int)
    requires 0 <= i < nums.len()
    ensures in_map(nums, m.insert(nums[i], i), t) ==> in_map(nums, m, t),
{
    assert forall|j: int| 0 <= j < nums.len() ==> m.insert(nums[i], i).contains_key(t - nums[j]) ==> m.contains_key(t - nums[j]) by {
        if j != i {
            assert(m.insert(nums[i], i).contains_key(t - nums[j]) == m.contains_key(t - nums[j]));
        }
    }
}

proof fn lemma_in_map_take(nums: Seq<int>, m: Map<int, int>, t: int, i: int)
    requires 0 <= i <= nums.len()
    ensures in_map(nums, m, t) ==> in_map(nums.take(i), m, t),
{
    assert forall|j: int| 0 <= j < i ==> m.contains_key(t - nums[j]) by {
        assert(0 <= j < nums.len());
    }
}

#[verifier::opaque]
spec fn ghost_map_to_verus_map(m: std::collections::HashMap<i32, i32>) -> Map<int, int> {
    |k: int| {
        if m.contains_key(&(k as i32)) {
            Some(m[&(k as i32)] as int)
        } else {
            None
        }
    }
}

proof fn lemma_ghost_map_to_verus_map_insert(m: std::collections::HashMap<i32, i32>, k: i32, v: i32)
    ensures ghost_map_to_verus_map(m.insert(k, v)) == ghost_map_to_verus_map(m).insert(k as int, v as int),
{
    reveal(ghost_map_to_verus_map);
    assert forall|x: int|
        ghost_map_to_verus_map(m.insert(k, v)).contains_key(x) == ghost_map_to_verus_map(m).insert(k as int, v as int).contains_key(x) by {
        reveal(ghost_map_to_verus_map);
    }
}

proof fn lemma_ghost_map_to_verus_map_contains(m: std::collections::HashMap<i32, i32>, k: i32)
    ensures m.contains_key(&k) == ghost_map_to_verus_map(m).contains_key(k as int),
{
    reveal(ghost_map_to_verus_map);
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
    let mut seen: std::collections::HashMap<i32, i32> = std::collections::HashMap::new();
    let mut i: i32 = 0;
    
    proof {
        lemma_in_map_empty(ghost_map_to_verus_map(seen), target as int);
    }
    
    while i < nums.len() as i32
        invariant 0 <= i <= nums.len() as i32
        invariant in_map(nums@.take(i as int), ghost_map_to_verus_map(seen), target as int)
        invariant forall|j: int, k: int| 0 <= j < k < i as int ==> nums@[j] + nums@[k] != target
    {
        let complement = target - nums[i as usize];
        if seen.contains_key(&complement) {
            let j = seen[&complement];
            return (j, i);
        }
        seen.insert(nums[i as usize], i);
        
        proof {
            lemma_ghost_map_to_verus_map_insert(seen, nums[i as usize], i);
            lemma_in_map_insert(nums@.take(i as int), ghost_map_to_verus_map(seen), target as int, (i-1) as int);
        }
        
        i += 1;
    }
    
    (-1, -1)
}
// </vc-code>

fn main() {}

}