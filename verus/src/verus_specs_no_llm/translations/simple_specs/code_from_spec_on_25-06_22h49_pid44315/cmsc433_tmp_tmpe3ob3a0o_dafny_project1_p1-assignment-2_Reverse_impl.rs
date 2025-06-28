use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<int>) -> (aRev: Vec<int>)
    ensures
        aRev.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> a.spec_index(i) == aRev.spec_index(aRev.len()-i-1),
{
    let mut aRev = Vec::new();
    let mut j: usize = 0;
    
    while j < a.len()
        invariant
            j <= a.len(),
            aRev.len() == j,
            forall |k: int| 0 <= k < j ==> a.spec_index((a.len() as int) - 1 - k) == aRev.spec_index(k),
    {
        let index = a.len() - 1 - j;
        aRev.push(a[index]);
        j = j + 1;
    }
    
    // Proof that the postcondition holds
    assert forall |i: int| 0 <= i < a.len() implies 
        a.spec_index(i) == aRev.spec_index((aRev.len() as int) - i - 1) by {
        
        // After the loop: j == a.len() and aRev.len() == a.len()
        assert(j == a.len());
        assert(aRev.len() == a.len());
        
        // Let k = aRev.len() - i - 1
        let k = (aRev.len() as int) - i - 1;
        
        // Show k is in valid range for the loop invariant
        assert(0 <= k < j) by {
            assert(0 <= i < a.len());
            assert(k == (a.len() as int) - i - 1);
            assert(k >= 0);
            assert(k < (a.len() as int));
            assert(j == a.len());
        }
        
        // From the loop invariant: a[(a.len() - 1 - k)] == aRev[k]
        assert(a.spec_index((a.len() as int) - 1 - k) == aRev.spec_index(k));
        
        // Show that (a.len() - 1 - k) == i
        assert((a.len() as int) - 1 - k == i) by {
            assert(k == (aRev.len() as int) - i - 1);
            assert(aRev.len() == a.len());
            // k = len - i - 1
            // len - 1 - k = len - 1 - (len - i - 1) = len - 1 - len + i + 1 = i
        }
        
        // Therefore: a[i] == aRev[k] where k = aRev.len() - i - 1
        assert(a.spec_index(i) == aRev.spec_index((aRev.len() as int) - i - 1));
    };
    
    aRev
}

}