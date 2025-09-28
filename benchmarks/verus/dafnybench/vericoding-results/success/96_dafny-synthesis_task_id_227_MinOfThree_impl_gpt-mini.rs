use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
// </vc-spec>
// <vc-code>
{
    if a <= b {
        if a <= c {
            a
        } else {
            c
        }
    } else {
        if b <= c {
            b
        } else {
            c
        }
    }
}
// </vc-code>

fn main() {
}

}