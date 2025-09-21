// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_recursive(a: Vec<i8>, i: usize, j: usize, x: i8) -> (result: isize)
    requires 
        i <= j,
        j <= a@.len(),
    ensures
        (i <= result && result < j as isize) || result == -1,
        result != -1 ==> a@[result as int] == x as int,
        result != -1 ==> forall|r: int| result < r && r < j as int ==> a@[r] != x as int,
        result == -1 ==> forall|r: int| i as int <= r && r < j as int ==> a@[r] != x as int,
    decreases j - i,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}