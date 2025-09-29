// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn count_distinct_colors(a: int, b: int, c: int) -> int {
    if a == b && b == c { 1 }
    else if a == b || b == c || a == c { 2 }
    else { 3 }
}

spec fn all_same(a: int, b: int, c: int) -> bool {
    a == b && b == c
}

spec fn exactly_two_same(a: int, b: int, c: int) -> bool {
    (a == b && b != c) || (b == c && a != b) || (a == c && a != b)
}

spec fn all_different(a: int, b: int, c: int) -> bool {
    a != b && b != c && a != c
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_cast_eq_preserves(a: i8, b: i8)
    ensures
        (a == b) ==> ((a as int) == (b as int)),
        (a != b) ==> ((a as int) != (b as int)),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        1 <= result as int <= 3,
        result as int == count_distinct_colors(a as int, b as int, c as int),
        result as int == 1 <==> all_same(a as int, b as int, c as int),
        result as int == 2 <==> exactly_two_same(a as int, b as int, c as int),
        result as int == 3 <==> all_different(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    if a == b && b == c {
        let r: i8 = 1;
        assert((a as int) == (b as int));
        assert((b as int) == (c as int));
        assert(all_same(a as int, b as int, c as int));
        assert(!exactly_two_same(a as int, b as int, c as int));
        assert(!all_different(a as int, b as int, c as int));
        assert(count_distinct_colors(a as int, b as int, c as int) == 1);
        assert(1 <= r as int);
        assert(r as int <= 3);
        r
    } else if a == b || b == c || a == c {
        let r: i8 = 2;
        // Not all three equal (since first branch didn't trigger)
        assert(!((a == b) && (b == c)));
        assert(!(((a as int) == (b as int)) && ((b as int) == (c as int))));
        // At least one pair equal
        assert((a as int) == (b as int) || (b as int) == (c as int) || (a as int) == (c as int));
        // Establish exactly_two_same by case analysis on which pair is equal
        if a == b {
            assert((a as int) == (b as int));
            assert(!(b == c));
            assert((b as int) != (c as int));
        } else if b == c {
            assert((b as int) == (c as int));
            assert(!(a == b));
            assert((a as int) != (b as int));
        } else {
            // a == c
            assert((a as int) == (c as int));
            assert(!(a == b));
            assert((a as int) != (b as int));
        }
        assert(exactly_two_same(a as int, b as int, c as int));
        assert(!all_same(a as int, b as int, c as int));
        assert(!all_different(a as int, b as int, c as int));
        assert(count_distinct_colors(a as int, b as int, c as int) == 2);
        assert(1 <= r as int);
        assert(r as int <= 3);
        r
    } else {
        let r: i8 = 3;
        assert((a as int) != (b as int));
        assert((b as int) != (c as int));
        assert((a as int) != (c as int));
        assert(!( (a as int) == (b as int) || (b as int) == (c as int) || (a as int) == (c as int) ));
        assert(all_different(a as int, b as int, c as int));
        assert(!all_same(a as int, b as int, c as int));
        assert(!exactly_two_same(a as int, b as int, c as int));
        assert(count_distinct_colors(a as int, b as int, c as int) == 3);
        assert(1 <= r as int);
        assert(r as int <= 3);
        r
    }
}
// </vc-code>


}

fn main() {}