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
    if a == b && b == c {
        // All three are equal
        3
    } else if a == b || b == c || a == c {
        // Exactly two are equal
        2
    } else {
        // All three are different
        1
    }
}
// </vc-code>

fn main() {}

}