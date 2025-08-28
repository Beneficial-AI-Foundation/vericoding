use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// </vc-spec>

// <vc-code>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
{
    let perimeter = 5 * side;
    perimeter
}
// </vc-code>

fn main() {
}

}