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
    
    // Establish initial invariant
    proof {
        assert(max_val == s.spec_index(0));
        assert(exists|k: int| 0 <= k < 1 && max_val == s.spec_index(k));
    }
    
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
                // Prove that max_val is still >= all previous elements
                assert(forall|j: int| 0 <= j < i ==> max_val >= s.spec_index(j));
                // Prove existence witness
                assert(max_val == s.spec_index(i as int));
                assert(exists|k: int| 0 <= k < (i + 1) && max_val == s.spec_index(k));
            }
        } else {
            proof {
                // max_val didn't change, so invariant is preserved
                assert(forall|j: int| 0 <= j < (i + 1) ==> max_val >= s.spec_index(j));
                assert(exists|k: int| 0 <= k < (i + 1) && max_val == s.spec_index(k));
            }
        }
        i += 1;
    }
    
    // Establish postcondition
    proof {
        assert(i == s.len());
        assert(forall|j: int| 0 <= j < s.len() ==> max_val >= s.spec_index(j));
        assert(exists|k: int| 0 <= k < s.len() && max_val == s.spec_index(k));
    }
    
    max_val
}

}