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
        forall|x: int| 0 <= x < a.len() ==> a.spec_index(mini as int) <= a.spec_index(x), // a.spec_index(mini) is the minimum value,
        forall|x: int| 0 <= x < mini ==> a.spec_index(mini as int) < a.spec_index(x), // a.spec_index(mini) is the first min
{
    let mut mini: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= mini < a.len(),
            1 <= i <= a.len(),
            mini < i,
            // mini is the index of minimum in a[0..i)
            forall|x: int| 0 <= x < i ==> a.spec_index(mini as int) <= a.spec_index(x),
            // mini is the first occurrence of minimum in a[0..i)
            forall|x: int| 0 <= x < mini ==> a.spec_index(mini as int) < a.spec_index(x),
    {
        if a.spec_index(i as int) < a.spec_index(mini as int) {
            mini = i;
        }
        
        i += 1;
    }
    
    // After the loop, we need to prove that the postconditions hold
    // At this point: i == a.len(), so we've considered all elements a[0..a.len())
    assert(i == a.len());
    
    // The invariant tells us that mini is minimum in a[0..i), which is now a[0..a.len())
    // This means mini is minimum in the entire array
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(mini as int) <= a.spec_index(x));
    
    // The invariant also tells us that mini is the first occurrence
    assert(forall|x: int| 0 <= x < mini ==> a.spec_index(mini as int) < a.spec_index(x));
    
    mini as nat
}

}