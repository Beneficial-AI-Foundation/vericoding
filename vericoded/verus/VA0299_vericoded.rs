// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    0 <= a <= 50 && 0 <= b <= 50 && 0 <= c <= 50
}

spec fn max_of_3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

spec fn sort_descending(a: int, b: int, c: int) -> (int, int, int) {
    if a >= b && a >= c {
        if b >= c { (a, b, c) } else { (a, c, b) }
    } else if b >= a && b >= c {
        if a >= c { (b, a, c) } else { (b, c, a) }
    } else {
        if a >= b { (c, a, b) } else { (c, b, a) }
    }
}

spec fn min_operations(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let (a0, a1, a2) = sort_descending(a, b, c);
    let gap1 = a0 - a1;
    let updated_smallest = a2 + gap1;
    let remaining_gap = a0 - updated_smallest;
    gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2
}

spec fn all_equal(a: int, b: int, c: int) -> bool {
    a == b && b == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove inputs non-negative */
fn lemma_valid_nonneg(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        0 <= a && 0 <= b && 0 <= c,
{
    proof {
        assert(0 <= a);
        assert(0 <= b);
        assert(0 <= c);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int),
    ensures
        result >= 0,
        all_equal(a as int, b as int, c as int) ==> result == 0,
        result as int == min_operations(a as int, b as int, c as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute min operations and return result */
    let a0: i8;
    let a1: i8;
    let a2: i8;

    if a >= b && a >= c {
        if b >= c {
            a0 = a; a1 = b; a2 = c;
        } else {
            a0 = a; a1 = c; a2 = b;
        }
    } else if b >= a && b >= c {
        if a >= c {
            a0 = b; a1 = a; a2 = c;
        } else {
            a0 = b; a1 = c; a2 = a;
        }
    } else {
        if a >= b {
            a0 = c; a1 = a; a2 = b;
        } else {
            a0 = c; a1 = b; a2 = a;
        }
    }

    let gap1_i8: i8 = a0 - a1;
    let updated_smallest_i8: i8 = a2 + gap1_i8;
    let remaining_gap_i8: i8 = a0 - updated_smallest_i8;
    let ops_i8: i8 = gap1_i8 + (remaining_gap_i8 / 2) + ((remaining_gap_i8 % 2) * 2);

    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        let ci: int = c as int;

        if ai >= bi && ai >= ci {
            if bi >= ci {
                assert(sort_descending(ai, bi, ci) == (ai, bi, ci));
            } else {
                assert(sort_descending(ai, bi, ci) == (ai, ci, bi));
            }
        } else if bi >= ai && bi >= ci {
            if ai >= ci {
                assert(sort_descending(ai, bi, ci) == (bi, ai, ci));
            } else {
                assert(sort_descending(ai, bi, ci) == (bi, ci, ai));
            }
        } else {
            if ai >= bi {
                assert(sort_descending(ai, bi, ci) == (ci, ai, bi));
            } else {
                assert(sort_descending(ai, bi, ci) == (ci, bi, ai));
            }
        }

        assert((a0 as int, a1 as int, a2 as int) == sort_descending(ai, bi, ci));

        let gap1: int = (a0 - a1) as int;
        let updated_smallest: int = (a2 as int) + gap1;
        let remaining_gap: int = (a0 as int) - updated_smallest;
        let ops_int: int = gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2;

        assert(ops_i8 as int == ops_int);
        assert(ops_int == min_operations(ai, bi, ci));
    }

    let result: i8 = ops_i8;
    result
}

// </vc-code>


}

fn main() {}