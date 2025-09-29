// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a1: int, a2: int, a3: int) -> bool {
    1 <= a1 <= 100 && 1 <= a2 <= 100 && 1 <= a3 <= 100
}

spec fn max_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 >= a2 && a1 >= a3 { a1 } else if a2 >= a3 { a2 } else { a3 }
}

spec fn min_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 <= a2 && a1 <= a3 { a1 } else if a2 <= a3 { a2 } else { a3 }
}

spec fn minimum_cost(a1: int, a2: int, a3: int) -> int {
    max_of_three(a1, a2, a3) - min_of_three(a1, a2, a3)
}
// </vc-preamble>

// <vc-helpers>
proof fn cmp_cast_equiv(x: i8, y: i8)
    ensures
        (x >= y) == ((x as int) >= (y as int)),
        (x <= y) == ((x as int) <= (y as int)),
        (x > y) == ((x as int) > (y as int)),
        (x < y) == ((x as int) < (y as int)),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, a3: i8) -> (result: i8)
    requires 
        valid_input(a1 as int, a2 as int, a3 as int)
    ensures 
        result as int >= 0,
        result as int == minimum_cost(a1 as int, a2 as int, a3 as int)
// </vc-spec>
// <vc-code>
{
    let maxv: i8 = if a1 >= a2 && a1 >= a3 { a1 } else if a2 >= a3 { a2 } else { a3 };
    let minv: i8 = if a1 <= a2 && a1 <= a3 { a1 } else if a2 <= a3 { a2 } else { a3 };

    let ghost maxi: int = max_of_three(a1 as int, a2 as int, a3 as int);
    let ghost mini: int = min_of_three(a1 as int, a2 as int, a3 as int);

    proof {
        if a1 >= a2 && a1 >= a3 {
            cmp_cast_equiv(a1, a2);
            cmp_cast_equiv(a1, a3);
            assert((a1 as int) >= (a2 as int));
            assert((a1 as int) >= (a3 as int));
            assert(maxi == a1 as int);
            assert(maxv as int == a1 as int);
        } else if a2 >= a3 {
            cmp_cast_equiv(a2, a3);
            assert((a2 as int) >= (a3 as int));
            assert(maxi == a2 as int);
            assert(maxv as int == a2 as int);
        } else {
            cmp_cast_equiv(a1, a2);
            cmp_cast_equiv(a1, a3);
            cmp_cast_equiv(a2, a3);
            assert(!((a1 as int) >= (a2 as int) && (a1 as int) >= (a3 as int)));
            assert(!((a2 as int) >= (a3 as int)));
            assert(maxi == a3 as int);
            assert(maxv as int == a3 as int);
        }

        if a1 <= a2 && a1 <= a3 {
            cmp_cast_equiv(a1, a2);
            cmp_cast_equiv(a1, a3);
            assert((a1 as int) <= (a2 as int));
            assert((a1 as int) <= (a3 as int));
            assert(mini == a1 as int);
            assert(minv as int == a1 as int);
        } else if a2 <= a3 {
            cmp_cast_equiv(a2, a3);
            assert((a2 as int) <= (a3 as int));
            assert(mini == a2 as int);
            assert(minv as int == a2 as int);
        } else {
            cmp_cast_equiv(a2, a3);
            assert(!((a1 as int) <= (a2 as int) && (a1 as int) <= (a3 as int)));
            assert(!((a2 as int) <= (a3 as int)));
            assert(mini == a3 as int);
            assert(minv as int == a3 as int);
        }

        assert(1 <= a1 as int && a1 as int <= 100);
        assert(1 <= a2 as int && a2 as int <= 100);
        assert(1 <= a3 as int && a3 as int <= 100);

        // Bounds for minv and maxv using that each equals one of a1, a2, a3
        assert(1 <= minv as int);
        assert(maxv as int <= 100);

        // Difference bounds ensure no overflow for i8 subtraction
        assert(0 <= (maxv as int) - (minv as int));
        assert((maxv as int) - (minv as int) <= 99);
    }

    let result: i8 = maxv - minv;

    proof {
        // Linking i8 arithmetic to int arithmetic (no overflow by bounds above)
        assert(result as int == (maxv as int) - (minv as int));
        assert(maxi == maxv as int);
        assert(mini == minv as int);
        assert(minimum_cost(a1 as int, a2 as int, a3 as int) == maxi - mini);
        assert(result as int == minimum_cost(a1 as int, a2 as int, a3 as int));
        assert(result as int >= 0);
    }

    result
}
// </vc-code>


}

fn main() {}