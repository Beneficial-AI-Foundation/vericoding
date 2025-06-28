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
        a.spec_index(i) == aRev.spec_index(aRev.len() - i - 1) by {
        
        // After the loop, j == a.len(), so aRev.len() == a.len()
        // The invariant gives us: forall k: 0 <= k < a.len() ==> a[(a.len() - 1 - k)] == aRev[k]
        
        // We want to show: a[i] == aRev[aRev.len() - i - 1]
        // Let k = aRev.len() - i - 1 = a.len() - i - 1
        let k = (a.len() as int) - i - 1;
        
        // Show k is in valid range: 0 <= k < a.len()
        assert(0 <= k < a.len()) by {
            // We know 0 <= i < a.len()
            assert(0 <= i < a.len());
            assert(k == (a.len() as int) - i - 1);
            // Since 0 <= i < a.len():
            // k = a.len() - i - 1 >= a.len() - (a.len()-1) - 1 = 0
            // k = a.len() - i - 1 < a.len() - 0 - 1 = a.len() - 1 < a.len()
            assert(k >= 0);
            assert(k < a.len());
        };
        
        // From the loop invariant with k in range:
        // a[(a.len() - 1 - k)] == aRev[k]
        assert(a.spec_index((a.len() as int) - 1 - k) == aRev.spec_index(k));
        
        // Show that (a.len() - 1 - k) == i
        assert((a.len() as int) - 1 - k == i) by {
            assert(k == (a.len() as int) - i - 1);
            // So: (a.len() - 1 - k) = a.len() - 1 - (a.len() - i - 1) = i
        };
        
        // Show that k == aRev.len() - i - 1
        assert(k == aRev.len() - i - 1) by {
            assert(aRev.len() == a.len());
            assert(k == (a.len() as int) - i - 1);
        };
        
        // Therefore: a[i] == a[(a.len() - 1 - k)] == aRev[k] == aRev[aRev.len() - i - 1]
        assert(a.spec_index(i) == a.spec_index((a.len() as int) - 1 - k));
        assert(a.spec_index((a.len() as int) - 1 - k) == aRev.spec_index(k));
        assert(aRev.spec_index(k) == aRev.spec_index(aRev.len() - i - 1));
    };
    
    aRev
}

}