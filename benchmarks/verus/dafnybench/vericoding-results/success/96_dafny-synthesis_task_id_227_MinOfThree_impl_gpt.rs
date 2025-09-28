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
            assert(a <= b);
            assert(c < a);
            assert(c <= a);
            assert(c <= b);
            c
        }
    } else {
        assert(b < a);
        if b <= c {
            assert(b <= a);
            b
        } else {
            assert(c < b);
            assert(c <= b);
            assert(b <= a);
            assert(c <= a);
            c
        }
    }
}
// </vc-code>

fn main() {
}

}