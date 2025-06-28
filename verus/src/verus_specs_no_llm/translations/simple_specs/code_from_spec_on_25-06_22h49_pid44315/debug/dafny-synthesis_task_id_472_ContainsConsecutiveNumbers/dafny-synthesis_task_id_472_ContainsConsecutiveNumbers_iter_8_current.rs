use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsConsecutiveNumbers(a: Vec<int>) -> (result: bool)
    requires
        a.len() > 0
    ensures
        result <==> (exists|i: int| 0 <= i < a.len() - 1 && a.spec_index(i) + 1 == a.spec_index(i + 1))
{
    if a.len() <= 1 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            a.len() > 1,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) + 1 != a.spec_index(j + 1)
        decreases a.len() - 1 - i
    {
        if a[i] + 1 == a[i + 1] {
            // Proof: We found consecutive numbers at position i
            assert(0 <= i < a.len() - 1);
            assert(a.spec_index(i as int) + 1 == a.spec_index((i + 1) as int));
            // Show that the witness exists
            assert(exists|k: int| 0 <= k < a.len() - 1 && a.spec_index(k) + 1 == a.spec_index(k + 1)) by {
                assert(0 <= i as int < a.len() - 1);
                assert(a.spec_index(i as int) + 1 == a.spec_index(i as int + 1));
            }
            return true;
        }
        i = i + 1;
    }
    
    // Proof: We've checked all positions and found no consecutive numbers
    assert(i == a.len() - 1);
    assert(forall|j: int| 0 <= j < a.len() - 1 ==> a.spec_index(j) + 1 != a.spec_index(j + 1)) by {
        // The invariant ensures we checked all positions from 0 to i-1
        // Since i == a.len() - 1, we checked all valid positions
        assert(forall|j: int| 0 <= j < i ==> a.spec_index(j) + 1 != a.spec_index(j + 1));
        // Since i == a.len() - 1, the range 0 <= j < i covers 0 <= j < a.len() - 1
    }
    
    // Show that no consecutive numbers exist
    assert(!(exists|k: int| 0 <= k < a.len() - 1 && a.spec_index(k) + 1 == a.spec_index(k + 1)));
    
    return false;
}

}