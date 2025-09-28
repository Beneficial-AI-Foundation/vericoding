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
spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}

proof fn lemma_map_contains_key_implies_index_in_bounds<A, B>(m: Map<A, B>, k: A)
    requires
        m.contains_key(k),
    ensures
        m.index_of(k) < m.len(),
{
}

proof fn lemma_vec_to_seq_index_correspondence(v: &[i32], i: int)
    requires
        0 <= i < v.len() as int,
    ensures
        v.view()[i] == v[i as usize],
{
}

proof fn lemma_map_insert_preserves_other_keys<A, B>(m: Map<A, B>, k1: A, k2: A, v: B)
    requires
        k1 != k2,
    ensures
        m.contains_key(k1) == m.insert(k2, v).contains_key(k1),
{
}

proof fn lemma_map_insert_new_key<A, B>(m: Map<A, B>, k: A, v: B)
    requires
        !m.contains_key(k),
    ensures
        m.insert(k, v).contains_key(k),
{
}

proof fn lemma_map_insert_preserves_all_keys<A, B>(m: Map<A, B>, k_new: A, v: B, k_old: A)
    ensures
        m.contains_key(k_old) ==> m.insert(k_new, v).contains_key(k_old),
{
    if m.contains_key(k_old) && k_new != k_old {
        lemma_map_insert_preserves_other_keys(m, k_old, k_new, v);
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
    let mut map = Map::<i32, usize>::empty();
    let n = nums.len();
    let mut j: usize = 0;
    
    while j < n
        invariant
            0 <= j <= n,
            forall|i: int| 0 <= i < j ==> map.contains_key(nums[i as usize]),
            forall|k: i32| map.contains_key(k) ==> (exists|i: int| 0 <= i < j && k == nums[i as usize] && map[k] == i),
            forall|p: int, q: int| 0 <= p < q < j ==> nums.view()[p] + nums.view()[q] != target,
    {
        let complement = target - nums[j];
        if map.contains_key(complement) {
            let i = map[complement];
            proof {
                lemma_vec_to_seq_index_correspondence(nums, i as int);
                lemma_vec_to_seq_index_correspondence(nums, j as int);
            }
            return (i as i32, j as i32);
        }
        
        proof {
            lemma_map_insert_new_key(map, nums[j], j);
            assert forall|k: i32| map.contains_key(k) implies map.insert(nums[j], j).contains_key(k) by {
                lemma_map_insert_preserves_all_keys(map, nums[j], j, k);
            };
        }
        map = map.insert(nums[j], j);
        j += 1;
    }
    
    (-1, -1)
}
// </vc-code>

fn main() {}

}