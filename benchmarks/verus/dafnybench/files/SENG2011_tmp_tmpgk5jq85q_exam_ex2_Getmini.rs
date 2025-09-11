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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}