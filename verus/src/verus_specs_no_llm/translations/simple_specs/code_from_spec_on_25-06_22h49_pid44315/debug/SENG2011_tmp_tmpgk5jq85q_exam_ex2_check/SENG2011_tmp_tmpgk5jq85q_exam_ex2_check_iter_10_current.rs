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
            mini < i, // mini is strictly less than i
            forall|x: int| 0 <= x < i ==> a[mini as int] <= a[x], // a[mini] is the minimum among elements 0..i
            forall|x: int| 0 <= x < mini ==> a[mini as int] < a[x], // a[mini] is the first occurrence of minimum in 0..mini
    {
        if a[i as int] < a[mini as int] {
            mini = i;
        }
        // If a[i] == a[mini], we don't update mini to maintain first occurrence property
        // If a[i] > a[mini], we don't update mini
        
        i = i + 1;
    }
    
    mini
}

}