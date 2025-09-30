// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int) -> bool {
    x > 0 && y > 0
}

spec fn no_even_in_range(x: int, y: int) -> bool {
    forall|i: int| x <= i <= y ==> #[trigger] (i % 2) != 0
}

spec fn is_largest_even_in_range(x: int, y: int, result: int) -> bool {
    result % 2 == 0 && 
    x <= result <= y && 
    (forall|i: int| x <= i <= y && #[trigger] (i % 2) == 0 ==> i <= result)
}

spec fn correct_result(x: int, y: int, result: int) -> bool {
    if x > y { 
        result == -1
    } else {
        (result == -1 && no_even_in_range(x, y)) ||
        is_largest_even_in_range(x, y, result)
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn top_even(y: int) -> int {
    if y % 2 == 0 { y } else { y - 1 }
}

proof fn lemma_top_even_props(y: int)
    ensures
        top_even(y) % 2 == 0,
        top_even(y) <= y,
        forall|i: int| i <= y && #[trigger] (i % 2) == 0 ==> i <= top_even(y),
{
    if y % 2 == 0 {
        assert(top_even(y) == y);
        assert(top_even(y) % 2 == 0);
        assert(top_even(y) <= y);
        assert forall|i: int| i <= y && #[trigger] (i % 2) == 0 ==> i <= top_even(y) by {
            if i <= y && i % 2 == 0 {
                assert(i <= y);
                assert(i <= top_even(y));
            }
        }
    } else {
        assert(y % 2 != 0);
        assert(top_even(y) == y - 1);
        assert(top_even(y) % 2 == 0);
        assert(top_even(y) <= y);
        assert forall|i: int| i <= y && #[trigger] (i % 2) == 0 ==> i <= top_even(y) by {
            if i <= y && i % 2 == 0 {
                // Show i <= y - 1 since y is odd and i is even
                if i == y {
                    // parity contradiction
                    assert((y % 2) == 1);
                    assert((i % 2) == 0);
                    assert(false);
                } else {
                    assert(i < y);
                    assert(i <= y - 1);
                }
            }
        }
    }
}

proof fn lemma_largest_even_when_top_ge_x(x: int, y: int)
    requires
        x <= y,
        top_even(y) >= x,
    ensures
        is_largest_even_in_range(x, y, top_even(y)),
{
    lemma_top_even_props(y);
    // result even and within [x, y]
    assert(top_even(y) % 2 == 0);
    assert(top_even(y) <= y);
    assert(x <= top_even(y));

    // maximality among evens in [x, y]
    assert forall|i: int| x <= i <= y && #[trigger] (i % 2) == 0 ==> i <= top_even(y) by {
        if x <= i && i <= y && i % 2 == 0 {
            assert(i <= y);
            assert(i <= top_even(y));
        }
    }
}

proof fn lemma_no_even_when_top_lt_x(x: int, y: int)
    requires
        x <= y,
        top_even(y) < x,
    ensures
        no_even_in_range(x, y),
{
    lemma_top_even_props(y);
    assert forall|i: int| x <= i <= y ==> #[trigger] (i % 2) != 0 by {
        if x <= i && i <= y {
            if i % 2 == 0 {
                assert(i <= y);
                assert(i <= top_even(y));
                assert(top_even(y) < x);
                assert(x <= i);
                assert(false);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn choose_num(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures correct_result(x as int, y as int, result as int)
// </vc-spec>
// <vc-code>
{
    if x > y {
        return -1;
    }

    let mut cand: i8;
    if y % 2 == 0 {
        cand = y;
    } else {
        proof { assert((y as int) >= 1); }
        cand = y - 1;
    }

    if cand >= x {
        proof {
            if y % 2 == 0 {
                assert((cand as int) == (y as int));
                assert(top_even(y as int) == y as int);
            } else {
                assert((cand as int) == (y as int) - 1);
                assert(top_even(y as int) == (y as int) - 1);
            }
            assert((cand as int) == top_even(y as int));
            assert(x as int <= y as int);
            assert(top_even(y as int) >= x as int);
            lemma_largest_even_when_top_ge_x(x as int, y as int);
        }
        cand
    } else {
        proof {
            if y % 2 == 0 {
                assert((cand as int) == (y as int));
                assert(top_even(y as int) == y as int);
            } else {
                assert((cand as int) == (y as int) - 1);
                assert(top_even(y as int) == (y as int) - 1);
            }
            assert((cand as int) == top_even(y as int));
            assert(top_even(y as int) < x as int);
            assert(x as int <= y as int);
            lemma_no_even_when_top_lt_x(x as int, y as int);
        }
        -1
    }
}
// </vc-code>


}

fn main() {}