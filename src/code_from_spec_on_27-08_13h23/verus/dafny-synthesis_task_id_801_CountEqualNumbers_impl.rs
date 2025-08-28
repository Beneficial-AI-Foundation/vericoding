use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was in the code structure
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_equal_numbers(a: i32, b: i32, c: i32) -> (count: i32)
    ensures 
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn count_equal_numbers(a: i32, b: i32, c: i32) -> (count: i32)
    ensures 
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
{
    let count = if a == b && b == c {
        3
    } else if (a == b && b != c) || (a != b && b == c) || (a == c && b != c) {
        2
    } else {
        1
    };
    count
}
// </vc-code>

fn main() {}

}