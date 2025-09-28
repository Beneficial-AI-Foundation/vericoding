// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_mini(a: &[i32]) -> (mini: usize)
    requires a.len() > 0,
    ensures 
        0 <= mini < a.len(),
        forall|x: usize| 0 <= x < a.len() ==> a[mini as int] <= a[x as int],
        forall|x: usize| 0 <= x < mini ==> a[mini as int] < a[x as int],
// </vc-spec>
// <vc-code>
{
    let mut mini: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= mini < i,
            forall|k: usize| 0 <= k < i ==> a[mini as int] <= a[k as int],
            forall|k: usize| 0 <= k < mini ==> a[mini as int] < a[k as int],
        decreases a.len() - i
    {
        if a[i] < a[mini] {
            mini = i;
        }
        i = i + 1;
    }
    mini
}
// </vc-code>

}
fn main() {}