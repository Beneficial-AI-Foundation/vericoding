use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_mini(a: &[i32]) -> (mini: usize)
    requires a.len() > 0,
    ensures 
        0 <= mini < a.len(), // mini is an index of a
        forall|x: usize| 0 <= x < a.len() ==> a[mini as int] <= a[x as int], // a[mini] is the minimum value
        forall|x: usize| 0 <= x < mini ==> a[mini as int] < a[x as int], // a[mini] is the first min
// </vc-spec>
// <vc-code>
{
    let mut mini: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 < a.len(),
            1 <= i <= a.len(),
            0 <= mini < i,
            mini < a.len(),
            forall|x: usize| 0 <= x < i ==> a@[mini as int] <= a@[x as int],
            forall|x: usize| 0 <= x < mini ==> a@[mini as int] < a@[x as int],
        decreases a.len() - i,
    {
        if a[i] < a[mini] {
            mini = i;
        }
        i = i + 1;
    }
    
    mini
}
// </vc-code>

fn main() {
}

}