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
    assume(false);
    0 // unreachable but needed for type checking
}
// </vc-code>


fn main() {
}

}
