use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Getmini(a: Vec<int>) -> (mini: nat)
    requires
        a.len() > 0
    ensures
        0 <= mini < a.len(), // mini is an index of a,
        forall|x: int| 0 <= x < a.len() ==> a.spec_index(mini) <= a.spec_index(x), // a.spec_index(mini) is the minimum value,
        forall|x: int| 0 <= x < mini ==> a.spec_index(mini) < a.spec_index(x), // a.spec_index(mini) is the first min
{
    let mut mini: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= mini < a.len(),
            1 <= i <= a.len(),
            // mini is the index of minimum in a[0..i]
            forall|x: int| 0 <= x < i ==> a.spec_index(mini) <= a.spec_index(x),
            // mini is the first occurrence of minimum in a[0..i]
            forall|x: int| 0 <= x < mini ==> a.spec_index(mini) < a.spec_index(x),
            mini < i,
    {
        if a[i] < a[mini] {
            mini = i;
        }
        i += 1;
    }
    
    // At this point, i == a.len(), so the invariants give us what we need
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(mini) <= a.spec_index(x));
    assert(forall|x: int| 0 <= x < mini ==> a.spec_index(mini) < a.spec_index(x));
    
    mini as nat
}

}