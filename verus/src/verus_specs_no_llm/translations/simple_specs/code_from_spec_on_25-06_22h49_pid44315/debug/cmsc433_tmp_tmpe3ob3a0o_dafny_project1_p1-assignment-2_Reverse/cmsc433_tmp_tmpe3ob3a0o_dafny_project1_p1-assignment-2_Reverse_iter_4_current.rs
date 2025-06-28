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
        // From the loop invariant, we know:
        // forall k: 0 <= k < a.len() ==> a[(a.len() - 1 - k)] == aRev[k]
        // We want to show: a[i] == aRev[aRev.len() - i - 1]
        // Let k = aRev.len() - i - 1 = a.len() - i - 1
        let k = (a.len() as int) - 1 - i;
        assert(0 <= k && k < a.len());
        assert((a.len() as int) - 1 - k == i);
        assert(k == aRev.len() - i - 1);
    };
    
    aRev
}

}