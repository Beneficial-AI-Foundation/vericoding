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
            found_negative <==> (exists|i: int| 1 <= i <= idx && s.spec_index(i) < 0),
            0 <= idx <= operations.len(),
    {
        current_sum = current_sum + operations.spec_index(idx as int);
        s.push(current_sum);
        
        if current_sum < 0 {
            found_negative = true;
            assert(s.spec_index((idx + 1) as int) < 0);
            assert(exists|i: int| 1 <= i <= idx + 1 && s.spec_index(i) < 0) by {
                assert(1 <= (idx + 1) as int <= idx + 1 && s.spec_index((idx + 1) as int) < 0);
            }
        } else {
            if !found_negative {
                assert forall|i: int| 1 <= i <= idx + 1 implies s.spec_index(i) >= 0 by {
                    if 1 <= i <= idx {
                        // follows from loop invariant
                    } else if i == idx + 1 {
                        assert(s.spec_index(i) == current_sum);
                        assert(current_sum >= 0);
                    }
                }
            }
        }
        
        idx = idx + 1;
    }
    
    // After the loop, prove the final properties
    assert(s.len() == operations.len() + 1);
    assert(s.spec_index(0) == 0);
    
    // Prove the cumulative sum property holds for the entire sequence
    assert forall|i: int| 0 <= i < s.len()-1 implies s.spec_index(i+1)==s.spec_index(i)+operations.spec_index(i) by {
        // This follows from the loop invariant when the loop completed
        assert(operations.len() == s.len() - 1);
        if 0 <= i < operations.len() {
            assert(i < idx);  // since idx == operations.len() after loop
        }
    };
    
    // Prove the negative detection properties
    if found_negative {
        // The loop invariant guarantees this
        assert(exists|i: int| 1 <= i <= operations.len() && s.spec_index(i) < 0) by {
            assert(exists|i: int| 1 <= i <= idx && s.spec_index(i) < 0);  // from invariant
            assert(idx == operations.len());  // loop terminated
        }
    } else {
        // Prove no negative values exist
        assert forall|i: int| 0 <= i < s.len() implies s.spec_index(i) >= 0 by {
            if i == 0 {
                assert(s.spec_index(0) == 0);
            } else if 1 <= i < s.len() {
                assert(i <= operations.len());
                assert(i <= idx);  // since idx == operations.len()
                // From loop invariant: !found_negative ==> no negative values up to idx
            }
        }
    }
    
    (s, found_negative)
}

}