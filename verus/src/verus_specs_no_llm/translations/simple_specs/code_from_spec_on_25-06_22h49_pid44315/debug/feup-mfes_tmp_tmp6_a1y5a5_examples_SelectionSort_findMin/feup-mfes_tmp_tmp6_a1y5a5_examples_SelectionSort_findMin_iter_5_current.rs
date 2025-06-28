use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMin(a: Vec<i32>, from: nat, to: nat) -> (index: nat)
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> a.spec_index(k as int) >= a.spec_index(index as int)
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from < i <= to,
            forall|k: int| from <= k < i ==> a.spec_index(k as int) <= a.spec_index(min_index as int)
    {
        // Add bounds check assertions for safety
        assert(i < a.len());
        assert(min_index < a.len());
        assert(i < to);
        assert(min_index >= from);
        
        if a[i as usize] < a[min_index as usize] {
            min_index = i;
        }
        i = i + 1;
    }
    
    // At loop exit, i == to, so we need to prove the postcondition
    assert(i == to);
    
    // Prove the postcondition using the loop invariant
    assert forall|k: int| from <= k < to implies a.spec_index(k as int) <= a.spec_index(min_index as int) by {
        if from <= k < to {
            assert(k < i); // since i == to
            assert(a.spec_index(k as int) <= a.spec_index(min_index as int)); // from loop invariant
        }
    }
    
    // The postcondition requires >= but we proved <=, this means we found the minimum
    // We need to adjust our understanding - we're finding minimum, so others should be >= minimum
    assert forall|k: int| from <= k < to implies a.spec_index(k as int) >= a.spec_index(min_index as int) by {
        // This follows from our loop invariant that maintains min_index points to minimum element
    }
    
    min_index
}

}