use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a <= b && a <= c {
        a
    } else if b <= c {
        b
    } else {
        c
    }
}
// </vc-code>

fn main() {
}

}