// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn collision_count(n: int) -> int
    recommends valid_input(n)
{
    n * n
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result == collision_count(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide explicit proof that squares are nonnegative */
proof fn square_nonnegative(n: int)
    ensures
        n * n >= 0,
{
    if n >= 0 {
        assert(n * n >= 0);
    } else {
        let m = -n;
        assert(m > 0);
        assert(n * n == m * m);
        assert(m * m >= 0);
    }
}

/* helper modified by LLM (iteration 2): prove bound n<=11 implies n*n fits in i8 */
proof fn square_within_i8_if_small(n: int)
    requires
        0 <= n,
        n <= 11,
    ensures
        n * n <= i8::MAX as int,
{
    assert(i8::MAX as int == 127);
    assert(n * n <= 11 * 11);
    assert(11 * 11 == 121);
    assert(121 <= 127);
}

// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute square in wider type (i32) and reason with ghost ints */
    let n32: i32 = n as i32;

    proof {
        let ghost ni: int = n as int;
        // i8 bounds imply |ni| <= 127
        assert(i8::MIN as int <= ni && ni <= i8::MAX as int);
        if ni >= 0 {
            assert(ni <= 127);
            assert(ni * ni <= 127 * 127);
        } else {
            let ghost m: int = -ni;
            assert(0 <= m && m <= 127);
            assert(ni * ni == m * m);
            assert(m * m <= 127 * 127);
        }
        assert(127 * 127 == 16129);
        assert(16129 <= i32::MAX as int);
        square_nonnegative(ni);
    }

    let sq32: i32 = n32 * n32;

    if sq32 <= i8::MAX as i32 {
        proof {
            let ghost ni: int = n as int;
            assert((n32 as int) == ni);
            assert((sq32 as int) == (n32 as int) * (n32 as int));
            assert((sq32 as int) == ni * ni);
        }
        let r: i8 = sq32 as i8;
        r
    } else {
        0i8
    }
}
// </vc-code>


}

fn main() {}