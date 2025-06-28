use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn below_zero(operations: Seq<int>) -> (s: Vec<int>, result: bool)
    requires operations.len() < usize::MAX
    ensures
        s.len() == operations.len() + 1,
        s.spec_index(0)==0,
        forall|i: int| 0 <= i < s.len()-1 ==> s.spec_index(i+1)==s.spec_index(i)+operations.spec_index(i),
        result == true ==> (exists|i: int| 1 <= i <= operations.len() && s.spec_index(i) < 0),
        result == false ==> forall|i: int| 0 <= i < s.len() ==> s.spec_index(i) >= 0
{
    let mut s = Vec::new();
    s.push(0);
    
    let mut current_sum = 0;
    let mut found_negative = false;
    
    let mut idx: usize = 0;
    while idx < operations.len()
        invariant
            s.len() == idx + 1,
            s.spec_index(0) == 0,
            current_sum == s.spec_index(idx as int),
            forall|i: int| 0 <= i < idx ==> s.spec_index(i+1)==s.spec_index(i)+operations.spec_index(i),
            found_negative == (exists|i: int| 1 <= i <= idx && s.spec_index(i) < 0),
            0 <= idx <= operations.len(),
    {
        current_sum = current_sum + operations.spec_index(idx as int);
        s.push(current_sum);
        
        if current_sum < 0 {
            found_negative = true;
        }
        
        idx = idx + 1;
    }
    
    // After the loop, prove the final properties
    assert(s.len() == operations.len() + 1);
    assert(s.spec_index(0) == 0);
    
    // Prove the cumulative sum property holds for the entire sequence
    assert forall|i: int| 0 <= i < s.len()-1 implies s.spec_index(i+1)==s.spec_index(i)+operations.spec_index(i) by {
        // This follows from the loop invariant since idx == operations.len() after loop
        assert(idx == operations.len());
        assert(s.len() == operations.len() + 1);
        if 0 <= i < s.len() - 1 {
            assert(i < operations.len());
            assert(i < idx);
        }
    };
    
    // Prove the negative detection properties
    if found_negative {
        assert(exists|i: int| 1 <= i <= operations.len() && s.spec_index(i) < 0) by {
            // From loop invariant: found_negative == (exists|i: int| 1 <= i <= idx && s.spec_index(i) < 0)
            // Since idx == operations.len() after loop completion
            assert(idx == operations.len());
        }
    } else {
        assert forall|i: int| 0 <= i < s.len() implies s.spec_index(i) >= 0 by {
            if i == 0 {
                assert(s.spec_index(0) == 0);
            } else if 1 <= i < s.len() {
                assert(i <= operations.len());
                assert(i <= idx);
                // From loop invariant: !found_negative means no negative values exist up to idx
                assert(!(exists|j: int| 1 <= j <= idx && s.spec_index(j) < 0));
                assert(s.spec_index(i) >= 0);
            }
        }
    }
    
    (s, found_negative)
}

}