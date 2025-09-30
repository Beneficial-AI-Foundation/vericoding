// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool
{
  a >= 1 && b >= 1
}

spec fn max_different_days(a: int, b: int) -> int
{
  if a < b { a } else { b }
}

spec fn remaining_after_different(a: int, b: int) -> int
{
  if a > b { a - max_different_days(a, b) } else { b - max_different_days(a, b) }
}

spec fn same_days(a: int, b: int) -> int
{
  remaining_after_different(a, b) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): maintain bounds lemma and adjust bridge lemma to avoid i8-int mixing by reasoning purely in ints */
proof fn lemma_basic_bounds(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        max_different_days(a, b) >= 0,
        max_different_days(a, b) <= a,
        max_different_days(a, b) <= b,
        remaining_after_different(a, b) >= 0,
        same_days(a, b) >= 0,
{
    if a < b {
        assert(max_different_days(a, b) == a);
        assert(max_different_days(a, b) <= a);
        assert(a <= b);
        assert(max_different_days(a, b) <= b);
        assert(a >= 1);
        assert(max_different_days(a, b) >= 0);
    } else {
        assert(max_different_days(a, b) == b);
        assert(max_different_days(a, b) <= b);
        assert(b <= a);
        assert(max_different_days(a, b) <= a);
        assert(b >= 1);
        assert(max_different_days(a, b) >= 0);
    }

    if a > b {
        assert(remaining_after_different(a, b) == a - max_different_days(a, b));
        assert(remaining_after_different(a, b) >= 0);
    } else {
        assert(remaining_after_different(a, b) == b - max_different_days(a, b));
        assert(remaining_after_different(a, b) >= 0);
    }

    assert(same_days(a, b) == remaining_after_different(a, b) / 2);
    assert(same_days(a, b) >= 0);
}

/* helper modified by LLM (iteration 3): bridge between i8 inputs and int specs using only int arithmetic */
proof fn lemma_bridge_i8(a: i8, b: i8)
    requires
        valid_input(a as int, b as int),
    ensures
        (if a < b { a } else { b }) as int == max_different_days(a as int, b as int),
        (if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) }) == remaining_after_different(a as int, b as int),
        ((if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) }) / 2) == same_days(a as int, b as int),
{
    // Bridge for max_different_days
    if (a as int) < (b as int) {
        assert(max_different_days(a as int, b as int) == a as int);
        assert((if a < b { a } else { b }) == a);
    } else {
        assert(max_different_days(a as int, b as int) == b as int);
        assert((if a < b { a } else { b }) == b);
    }

    let minv_int: int = if (a as int) < (b as int) { a as int } else { b as int };

    // Bridge for remaining_after_different (pure int arithmetic)
    if (a as int) > (b as int) {
        assert(remaining_after_different(a as int, b as int)
            == (a as int) - max_different_days(a as int, b as int));
        assert(max_different_days(a as int, b as int) == minv_int);
        assert((if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) })
            == (a as int) - minv_int);
        assert(remaining_after_different(a as int, b as int)
            == (if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) }));
    } else {
        assert(remaining_after_different(a as int, b as int)
            == (b as int) - max_different_days(a as int, b as int));
        assert(max_different_days(a as int, b as int) == minv_int);
        assert((if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) })
            == (b as int) - minv_int);
        assert(remaining_after_different(a as int, b as int)
            == (if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) }));
    }

    // Bridge for same_days via definition and the above equality
    assert(same_days(a as int, b as int) == remaining_after_different(a as int, b as int) / 2);
    assert(((if (a as int) > (b as int) { (a as int) - ((if a < b { a } else { b }) as int) } else { (b as int) - ((if a < b { a } else { b }) as int) }) / 2)
        == same_days(a as int, b as int));
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
  requires valid_input(a as int, b as int)
  ensures ({
      let (days_different, days_same) = result;
      days_different as int == max_different_days(a as int, b as int) &&
      days_same as int == same_days(a as int, b as int) &&
      days_different >= 0 &&
      days_same >= 0 &&
      days_different <= a && days_different <= b
  })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): compute answers in i8; use helper lemmas for spec linkage */
{
    let days_different: i8 = if a < b { a } else { b };
    let remaining: i8 = if a > b { a - days_different } else { b - days_different };
    let days_same: i8 = remaining / 2;

    proof {
        // Use helper lemmas to relate i8 computations to int specs
        lemma_basic_bounds(a as int, b as int);
        lemma_bridge_i8(a, b);

        // Match our variables to the expressions used in the bridge lemma
        assert((days_different as int) == max_different_days(a as int, b as int));
        // We rely on the definition of same_days and the helper bridges for final equality
        assert((days_same as int) == same_days(a as int, b as int));

        // Simple bounds for days_different relative to a and b
        if a < b {
            assert(days_different == a);
            assert(days_different <= b) by { assert(a <= b); };
        } else {
            assert(days_different == b);
            assert(days_different <= a) by { assert(b <= a); };
        }
    }

    (days_different, days_same)
}
// </vc-code>


}

fn main() {}