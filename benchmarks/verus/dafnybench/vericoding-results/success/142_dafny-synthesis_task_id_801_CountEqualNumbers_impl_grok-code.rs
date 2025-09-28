use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_equal_numbers(a: i32, b: i32, c: i32) -> (count: i32)
    ensures 
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
// </vc-spec>
// <vc-code>
{
    let dist = if a == b && b == c {
        1
    } else if (a == b || b == c || a == c) {
        2
    } else {
        3
    };
    let count = 4 - dist;
    count
}
// </vc-code>

fn main() {}

}