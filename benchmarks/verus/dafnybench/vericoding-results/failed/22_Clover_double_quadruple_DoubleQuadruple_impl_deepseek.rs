use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn double_quadruple_lemma(x: int)
    ensures
        2 * x == 2 * x,
        4 * x == 4 * x,
{
}

proof fn arithmetic_bounds_lemma(x: int)
    requires
        x >= -1073741824 && x <= 1073741823,
    ensures
        -2147483648 <= 2 * x <= 2147483647,
        -2147483648 <= 4 * x <= 2147483647,
{
    assert(2 * x >= -2147483648) by {
        assert(x >= -1073741824);
        assert(2 * x >= 2 * -1073741824);
        assert(2 * -1073741824 == -2147483648);
    };
    assert(2 * x <= 2147483647) by {
        assert(x <= 1073741823);
        assert(2 * x <= 2 * 1073741823);
        assert(2 * 1073741823 == 2147483646);
    };
    assert(4 * x >= -2147483648) by {
        assert(x >= -1073741824);
        assert(4 * x >= 4 * -1073741824);
        assert(4 * -1073741824 == -4294967296);
    };
    assert(4 * x <= 2147483647) by {
        assert(x <= 1073741823);
        assert(4 * x <= 4 * 1073741823);
        assert(4 * 1073741823 == 4294967292);
    };
}
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (ret: (i32, i32))
  ensures ret.0 == 2 * x && ret.1 == 4 * x
// </vc-spec>
// <vc-code>
{
    proof {
        double_quadruple_lemma(x as int);
        arithmetic_bounds_lemma(x as int);
    }
    assert(-2147483648 <= 2 * x && 2 * x <= 2147483647) by { arithmetic_bounds_lemma(x as int); };
    assert(-2147483648 <= 4 * x && 4 * x <= 2147483647) by { arithmetic_bounds_lemma(x as int); };
    (2 * x, 4 * x)
}
// </vc-code>

fn main() {}

}