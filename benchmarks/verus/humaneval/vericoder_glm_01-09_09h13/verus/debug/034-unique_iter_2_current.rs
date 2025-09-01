use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
fn find_min_index_and_value(v: &Vec<i32>) -> (index: int, value: i32)
    requires
        v.len() > 0
    ensures
        0 <= index < v.len(),
        value == v@[index],
        forall|i: int| 0 <= i < v.len() ==> v@[index] <= v@[i]
{
    let mut min_index = 0;
    let mut min_value = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= min_index < v.len(),
            min_value == v@[min_index],
            forall|k: int| 0 <= k < i ==> v@[min_index] <= v@[k],
            1 <= i <= v.len()
    {
        if v[i] < min_value {
            min_index = i;
            min_value = v[i];
        }
        i += 1;
    }
    
    proof {
        assert forall|k: int| 0 <= k < v.len() implies v@[min_index] <= v@[k] by {
            if k < i {
                assert(v@[min_index] <= v@[k]);
            } else {
                assert(v@[min_index] <= v@[k]);
            }
        }
    }
    
    (min_index, min_value)
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut temp = s.clone();
    
    while temp.len() > 0
        invariant
            result.len() + temp.len() == s.len(),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
            forall|i: int| 0 <= i < result.len() ==> s@.contains(result[i]),
            forall|i: int| 0 <= i < temp.len() ==> s@.contains(temp[i]),
            forall|i: int| 0 <= i < s.len() ==> result@.contains(s[i]) || temp@.contains(s[i])
    {
        let (min_index, min_value) = find_min_index_and_value(&temp);
        
        if result.len() == 0 || result[result.len() - 1] < min_value {
            result.push(min_value);
        }
        
        temp.remove(min_index as usize);
    }
    
    result
}
// </vc-code>

fn main() {}
}