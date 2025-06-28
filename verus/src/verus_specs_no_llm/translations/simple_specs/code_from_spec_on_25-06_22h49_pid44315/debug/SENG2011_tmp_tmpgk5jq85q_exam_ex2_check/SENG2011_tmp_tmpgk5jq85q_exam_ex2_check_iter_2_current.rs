use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Getmini(a: Vec<int>) -> (mini: usize) 
    requires 
        a.len() > 0
    ensures 
        mini < a.len(), // mini is an index of a
        forall|x: int| 0 <= x < a.len() ==> a[mini as int] <= a[x], // a[mini] is the minimum value
        forall|x: int| 0 <= x < mini ==> a[mini as int] < a[x], // a[mini] is the first min
{
    let mut mini: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= mini < a.len(),
            1 <= i <= a.len(),
            mini < i, // mini is always less than i
            forall|x: int| 0 <= x < mini ==> a[mini as int] < a[x], // a[mini] is strictly less than all previous elements
            forall|x: int| mini < x < i ==> a[mini as int] <= a[x], // a[mini] is less than or equal to elements after mini but before i
            forall|x: int| 0 <= x < i ==> a[mini as int] <= a[x], // a[mini] is the minimum among elements 0..i
    {
        if a[i as int] < a[mini as int] {
            mini = i;
        } else {
            // When we don't update mini, we need to assert that a[mini] <= a[i]
            assert(a[mini as int] <= a[i as int]);
        }
        i = i + 1;
    }
    
    // At this point i == a.len(), so we've checked all elements
    assert(i == a.len());
    assert(forall|x: int| 0 <= x < a.len() ==> a[mini as int] <= a[x]);
    
    mini
}

}