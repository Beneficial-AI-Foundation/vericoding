// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(k: int, a: int, b: int) -> bool {
  k > 0 && a <= b
}

spec fn floor_div(a: int, b: int) -> int {
  if a >= 0 { a / b }
  else { (a - b + 1) / b }
}

spec fn count_divisibles_in_range(k: int, a: int, b: int) -> int {
  floor_div(b, k) - floor_div(a - 1, k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemmas for floor_div monotonicity and non-negativity of the count */
proof fn floor_div_monotonic_lemma(k: int, x: int, y: int)
    requires
        k > 0,
        x <= y,
    ensures
        floor_div(x, k) <= floor_div(y, k),
{
    if x >= 0 && y >= 0 {
        assert(floor_div(x, k) == x / k);
        assert(floor_div(y, k) == y / k);
        assert(x / k <= y / k);
    } else if x < 0 && y < 0 {
        assert(floor_div(x, k) == (x - k + 1) / k);
        assert(floor_div(y, k) == (y - k + 1) / k);
        assert(x - k + 1 <= y - k + 1);
        assert((x - k + 1) / k <= (y - k + 1) / k);
    } else {
        assert(x < 0 && y >= 0);
        assert(floor_div(y, k) == y / k);
        assert(floor_div(x, k) <= 0);
        assert(0 <= y / k);
        assert(floor_div(x, k) <= floor_div(y, k));
    }
}

/* helper modified by LLM (iteration 2): Non-negativity of count_divisibles_in_range */
proof fn count_nonneg_lemma(k: int, a: int, b: int)
    requires
        valid_input(k, a, b),
    ensures
        count_divisibles_in_range(k, a, b) >= 0,
{
    floor_div_monotonic_lemma(k, a - 1, b);
    assert(floor_div(a - 1, k) <= floor_div(b, k));
    assert(count_divisibles_in_range(k, a, b) == floor_div(b, k) - floor_div(a - 1, k));
    assert(floor_div(b, k) - floor_div(a - 1, k) >= 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8) -> (result: i8)
  requires
    valid_input(k as int, a as int, b as int),
  ensures
    result >= 0,
    result as int == count_divisibles_in_range(k as int, a as int, b as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute using i32 to avoid ghost ints in exec code and relate to spec via proof */
    let ki32: i32 = k as i32;
    let ai32: i32 = a as i32;
    let bi32: i32 = b as i32;

    // compute t = a - 1 in i32 to avoid i8 underflow
    let ti32: i32 = ai32 - 1;

    // floor_div on bi32
    let fb: i32 = if bi32 >= 0 { bi32 / ki32 } else { (bi32 - ki32 + 1) / ki32 };
    // floor_div on (a - 1)
    let fa1: i32 = if ti32 >= 0 { ti32 / ki32 } else { (ti32 - ki32 + 1) / ki32 };

    let res_i32: i32 = fb - fa1;
    let result: i8 = res_i32 as i8;

    proof {
        // Given precondition, the spec count is non-negative
        assert(valid_input(k as int, a as int, b as int));
        count_nonneg_lemma(k as int, a as int, b as int);

        // Relate fb to floor_div(b, k)
        if bi32 >= 0 {
            assert(floor_div(b as int, k as int) == (b as int) / (k as int));
            assert(((bi32 / ki32) as int) == (bi32 as int) / (ki32 as int));
            assert((fb as int) == floor_div(b as int, k as int));
        } else {
            assert(floor_div(b as int, k as int) == ((b as int) - (k as int) + 1) / (k as int));
            assert(((bi32 - ki32 + 1) as int) == (bi32 as int) - (k as int) + 1);
            assert((((bi32 - ki32 + 1) / ki32) as int) == (((bi32 as int) - (k as int) + 1) / (ki32 as int)));
            assert((fb as int) == floor_div(b as int, k as int));
        }

        // Relate fa1 to floor_div(a - 1, k)
        if ti32 >= 0 {
            assert(floor_div((a as int) - 1, k as int) == (((a as int) - 1) / (k as int)));
            assert(((ti32 / ki32) as int) == (ti32 as int) / (ki32 as int));
            assert((fa1 as int) == floor_div((a as int) - 1, k as int));
        } else {
            assert(floor_div((a as int) - 1, k as int) == ((((a as int) - 1) - (k as int) + 1) / (k as int)));
            assert(((ti32 - ki32 + 1) as int) == (ti32 as int) - (k as int) + 1);
            assert((((ti32 - ki32 + 1) / ki32) as int) == (((ti32 as int) - (k as int) + 1) / (ki32 as int)));
            assert((fa1 as int) == floor_div((a as int) - 1, k as int));
        }

        // Combine to match the spec count
        assert((res_i32 as int) == (fb as int) - (fa1 as int));
        assert((res_i32 as int) == count_divisibles_in_range(k as int, a as int, b as int));

        // Connect the returned value to the spec result
        assert(result as int == res_i32 as int);
        assert(result as int == count_divisibles_in_range(k as int, a as int, b as int));
    }

    result
}
// </vc-code>


}

fn main() {}