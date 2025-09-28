use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
        assert(a == b && b == c);
        3
    } else if a == b && b != c {
        // a and b are equal, but different from c
        assert((a == b && b != c) || (a != b && b == c) || (a == c && b != c));
        2
    } else if a != b && b == c {
        // b and c are equal, but different from a
        assert((a == b && b != c) || (a != b && b == c) || (a == c && b != c));
        2
    } else if a == c && b != c {
        // a and c are equal, but different from b
        assert((a == b && b != c) || (a != b && b == c) || (a == c && b != c));
        2
    } else {
        // All three are different
        assert(a != b && b != c && a != c);
        1
    }
}
// </vc-code>

fn main() {}

}