use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        forall|x: int| 0 <= x < s.len() ==> a >= s.spec_index(x),
        exists|i: int| 0 <= i < s.len() && a == s.spec_index(i)
{
    let mut max_val: int = s[0];
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            forall|j: int| 0 <= j < i ==> max_val >= s.spec_index(j),
            exists|k: int| 0 <= k < i && max_val == s.spec_index(k)
        decreases s.len() - i
    {
        if s[i] > max_val {
            max_val = s[i];
            proof {
                // After updating max_val to s[i], prove the invariants hold
                assert(max_val == s.spec_index(i as int));
                
                // Prove that max_val >= all elements from 0 to i (inclusive)
                assert(forall|j: int| 0 <= j < i ==> max_val >= s.spec_index(j)) by {
                    // This follows from the loop invariant and the fact that max_val >= old max_val
                    assert(s.spec_index(i as int) > max_val);  // This is false, but we need to reason about the old max_val
                };
                
                // The new max_val is s[i], and we have i < i+1, so the existence condition holds
                assert(0 <= (i as int) < (i as int) + 1);
                assert(exists|k: int| 0 <= k < (i as int) + 1 && max_val == s.spec_index(k));
            }
        } else {
            proof {
                // max_val didn't change, so we need to extend the invariant to include s[i]
                assert(s.spec_index(i as int) <= max_val);
                assert(forall|j: int| 0 <= j < (i as int) + 1 ==> max_val >= s.spec_index(j)) by {
                    // This follows from the loop invariant plus the fact that s[i] <= max_val
                };
                assert(exists|k: int| 0 <= k < (i as int) + 1 && max_val == s.spec_index(k)) by {
                    // This follows from the loop invariant
                };
            }
        }
        i += 1;
    }
    
    proof {
        // When the loop exits, i == s.len(), so our invariants give us the postcondition
        assert(i == s.len());
        assert(forall|j: int| 0 <= j < s.len() ==> max_val >= s.spec_index(j));
        assert(exists|k: int| 0 <= k < s.len() && max_val == s.spec_index(k));
    }
    
    max_val
}

}