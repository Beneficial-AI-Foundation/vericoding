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

// Helper lemma to prove that insertion preserves sorted order
proof fn lemma_insert_preserves_sorted(v: Seq<i32>, pos: int, val: i32)
    requires
        0 <= pos <= v.len(),
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j],
        forall|i: int| 0 <= i < pos ==> v[i] < val,
        forall|i: int| pos <= i < v.len() ==> v[i] >= val,  // Changed from > to >=
    ensures
        forall|i: int, j: int| 0 <= i < j < v.insert(pos, val).len() ==> v.insert(pos, val)[i] < v.insert(pos, val)[j],
{
    assert forall|i: int, j: int| 0 <= i < j < v.insert(pos, val).len() implies 
        v.insert(pos, val)[i] < v.insert(pos, val)[j] by {
        if i < pos && j == pos {
            assert(v.insert(pos, val)[i] == v[i]);
            assert(v.insert(pos, val)[j] == val);
        } else if i < pos && j > pos {
            assert(v.insert(pos, val)[i] == v[i]);
            assert(v.insert(pos, val)[j] == v[j - 1]);
        } else if i == pos && j > pos {
            assert(v.insert(pos, val)[i] == val);
            assert(v.insert(pos, val)[j] == v[j - 1]);
        } else if i > pos && j > pos {
            assert(v.insert(pos, val)[i] == v[i - 1]);
            assert(v.insert(pos, val)[j] == v[j - 1]);
        }
    }
}

// Helper lemma for containment after insertion
proof fn lemma_insert_preserves_contains(v: Seq<i32>, pos: int, val: i32, s: Seq<i32>, bound: int)
    requires
        0 <= pos <= v.len(),
        0 <= bound <= s.len(),
        forall|k: int| 0 <= k < bound && s[k] != val ==> v.contains(s[k]),
    ensures
        forall|k: int| 0 <= k < bound ==> v.insert(pos, val).contains(s[k]),
{
    assert forall|k: int| 0 <= k < bound implies v.insert(pos, val).contains(s[k]) by {
        if s[k] == val {
            assert(v.insert(pos, val)[pos] == val);
        } else {
            let idx = choose|m: int| 0 <= m < v.len() && v[m] == s[k];
            if idx < pos {
                assert(v.insert(pos, val)[idx] == s[k]);
            } else {
                assert(v.insert(pos, val)[idx + 1] == s[k]);
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
        decreases s.len() - i,
    {
        let val = s[i];
        
        // Check if val is already in result
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> exists|k: int| 0 <= k < result.len() && result[k] == val,  // Fixed: use result.len() instead of j
                !found ==> forall|k: int| 0 <= k < j ==> result[k] != val,
            decreases result.len() - j,
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
                    insert_pos < result.len() ==> result[insert_pos as int] >= val,  // Fixed: removed disjunction
                decreases result.len() - insert_pos,
            {
                insert_pos = insert_pos + 1;
            }
            
            // Save the old result for proof
            let ghost old_result = result@;
            
            // Insert val at insert_pos
            result.insert(insert_pos, val);
            
            // Prove the invariants are maintained
            proof {
                // Establish preconditions for lemma
                assert(forall|k: int| 0 <= k < insert_pos ==> old_result[k] < val);
                assert(forall|k: int| insert_pos <= k < old_result.len() ==> old_result[k] >= val);
                
                // Prove sorted property is maintained
                lemma_insert_preserves_sorted(old_result, insert_pos as int, val);
                
                // Prove all elements in result are from s
                assert forall|k: int| 0 <= k < result.len() implies s@.contains(result[k]) by {
                    if k == insert_pos {
                        assert(result[k] == val);
                        assert(s[i as int] == val);
                        assert(s@.contains(val));
                    } else if k < insert_pos {
                        assert(result[k] == old_result[k]);
                    } else {
                        assert(result[k] == old_result[k - 1]);
                    }
                }
                
                // Prove containment properties for elements processed so far
                lemma_insert_preserves_contains(old_result, insert_pos as int, val, s@, i + 1);
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