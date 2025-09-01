use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
// Helper function to check if a value exists in a vector
spec fn contains_value(v: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == val
}

// Helper lemma to prove that if we add an element not in the sequence, 
// all previous containment relationships are preserved
proof fn lemma_push_preserves_contains(s: Seq<i32>, v: Seq<i32>, new_val: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> v.contains(s[i]),
    ensures
        forall|i: int| 0 <= i < s.len() ==> v.push(new_val).contains(s[i]),
{
    assert forall|i: int| 0 <= i < s.len() implies v.push(new_val).contains(#[trigger] s[i]) by {
        let idx = choose|j: int| 0 <= j < v.len() && v[j] == s[i];
        assert(0 <= idx < v.len() && v[idx] == s[i]);
        assert(v.push(new_val)[idx] == s[i]);
    }
}

// Helper lemma for sorted property preservation
proof fn lemma_sorted_push(v: Seq<i32>, new_val: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j],
        forall|i: int| 0 <= i < v.len() ==> v[i] < new_val,
    ensures
        forall|i: int, j: int| 0 <= i < j < v.push(new_val).len() ==> v.push(new_val)[i] < v.push(new_val)[j],
{
    assert forall|i: int, j: int| 0 <= i < j < v.push(new_val).len() implies 
        v.push(new_val)[i] < v.push(new_val)[j] by {
        if j < v.len() {
            assert(v.push(new_val)[i] == v[i]);
            assert(v.push(new_val)[j] == v[j]);
        } else {
            assert(j == v.len());
            assert(v.push(new_val)[j] == new_val);
            if i < v.len() {
                assert(v.push(new_val)[i] == v[i]);
            }
        }
    }
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] < result[j],
            forall|k: int| #![auto] 0 <= k < result.len() ==> s@.contains(result[k]),
            forall|k: int| #![trigger s[k]] 0 <= k < i ==> result@.contains(s[k]),
    {
        let val = s[i];
        
        // Check if val is already in result
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> exists|k: int| 0 <= k < j && result[k] == val,
                !found ==> forall|k: int| 0 <= k < j ==> result[k] != val,
        {
            if result[j] == val {
                found = true;
                assert(result@.contains(val));
                break;
            }
            j = j + 1;
        }
        
        if !found {
            // Find the correct position to insert val to maintain sorted order
            let mut insert_pos: usize = 0;
            
            while insert_pos < result.len() && result[insert_pos] < val
                invariant
                    0 <= insert_pos <= result.len(),
                    forall|k: int| 0 <= k < insert_pos ==> result[k] < val,
                    insert_pos < result.len() ==> result[insert_pos as int] >= val || insert_pos == result.len(),
            {
                insert_pos = insert_pos + 1;
            }
            
            // Insert val at insert_pos
            result.insert(insert_pos, val);
            
            // Prove the invariants are maintained
            proof {
                // Prove sorted property is maintained
                assert forall|k: int, m: int| 0 <= k < m < result.len() implies result[k] < result[m] by {
                    if k < insert_pos && m == insert_pos {
                        assert(result[k] == old(result)[k]);
                        assert(result[m] == val);
                    } else if k < insert_pos && m > insert_pos {
                        assert(result[k] == old(result)[k]);
                        assert(result[m] == old(result)[m - 1]);
                    } else if k == insert_pos && m > insert_pos {
                        assert(result[k] == val);
                        assert(result[m] == old(result)[m - 1]);
                    } else if k > insert_pos && m > insert_pos {
                        assert(result[k] == old(result)[k - 1]);
                        assert(result[m] == old(result)[m - 1]);
                    }
                }
                
                // Prove containment properties
                assert forall|k: int| 0 <= k <= i implies result@.contains(#[trigger] s[k]) by {
                    if k == i {
                        assert(result[insert_pos as int] == val);
                        assert(result@.contains(val));
                    } else if k < i {
                        if old(result)@.contains(s[k]) {
                            let idx = choose|m: int| 0 <= m < old(result).len() && old(result)[m] == s[k];
                            if idx < insert_pos {
                                assert(result[idx] == s[k]);
                            } else {
                                assert(result[idx + 1] == s[k]);
                            }
                        }
                    }
                }
            }
        } else {
            assert(result@.contains(val));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}